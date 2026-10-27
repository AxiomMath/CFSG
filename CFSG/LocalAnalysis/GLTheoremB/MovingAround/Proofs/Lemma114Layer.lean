module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Defs
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma114Layer

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

variable {Y : Type} [Group Y]

theorem eq_one_of_pow_eq_one {p : ℕ} [hp : Fact p.Prime] {z : Y} {m k : ℕ}
    (hm : ¬ p ∣ m) (hz : z ^ m = 1) (hk : z ^ (p ^ k) = 1) : z = 1 := by
  have h1 : orderOf z ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf z ∣ m := orderOf_dvd_of_pow_eq_one hz
  have hc : Nat.Coprime (p ^ k) m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  have h3 : orderOf z ∣ Nat.gcd (p ^ k) m := Nat.dvd_gcd h1 h2
  rw [hc.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem mem_of_pow_pow_mem {p : ℕ} [hp : Fact p.Prime] {S : Subgroup Y} {z : Y} {m k : ℕ}
    (hm : ¬ p ∣ m) (hz : z ^ m = 1) (hk : z ^ (p ^ k) ∈ S) : z ∈ S := by
  have hc : IsCoprime ((p ^ k : ℕ) : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (z ^ (p ^ k)) ^ u = z ^ (u * ((p ^ k : ℕ) : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have h2 : (z ^ m) ^ v = z ^ (v * (m : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have key : z = (z ^ (p ^ k)) ^ u * (z ^ m) ^ v := by
    rw [h1, h2, ← zpow_add, huv, zpow_one]
  rw [key]
  exact S.mul_mem (S.zpow_mem hk u) (by simp [hz])

theorem conj_pow_mem {M : Subgroup Y} {b : Y} (hb : ∀ x ∈ M, b * x * b⁻¹ ∈ M) (n : ℕ) :
    ∀ x ∈ M, b ^ n * x * (b ^ n)⁻¹ ∈ M := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    have h1 := hb _ (ih x hx)
    have e : b ^ (n + 1) * x * (b ^ (n + 1))⁻¹ = b * (b ^ n * x * (b ^ n)⁻¹) * b⁻¹ := by
      group
    rw [e]
    exact h1

theorem exists_mul_pow_eq {M : Subgroup Y} {b : Y} (hb : ∀ x ∈ M, b * x * b⁻¹ ∈ M)
    {l : Y} (hl : l ∈ M) (n : ℕ) : ∃ l' ∈ M, (l * b) ^ n = l' * b ^ n := by
  induction n with
  | zero => exact ⟨1, M.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', he⟩ := ih
    refine ⟨l' * (b ^ n * l * (b ^ n)⁻¹), M.mul_mem hl' (conj_pow_mem hb n l hl), ?_⟩
    rw [pow_succ, he]
    group

theorem mem_of_pow_eq_one_of_mem_sup {p : ℕ} [hp : Fact p.Prime] {L Z : Subgroup Y} [L.Normal]
    (hZ : ∀ z ∈ Z, ¬ p ∣ orderOf z) {x : Y} (hx : x ∈ L ⊔ Z) {k : ℕ}
    (hk : x ^ (p ^ k) = 1) : x ∈ L := by
  obtain ⟨l, hl, z, hz, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := L) (t := Z)).1 hx
  have hb : ∀ y ∈ L, z * y * z⁻¹ ∈ L := fun y hy => Subgroup.Normal.conj_mem ‹L.Normal› y hy z
  obtain ⟨l', hl', he⟩ := exists_mul_pow_eq hb hl (p ^ k)
  have hzp : z ^ (p ^ k) ∈ L := by
    have h1 : l' * z ^ (p ^ k) = 1 := by rw [← he, hk]
    rw [eq_inv_of_mul_eq_one_right h1]; exact L.inv_mem hl'
  have hzm : z ^ orderOf z = 1 := pow_orderOf_eq_one z
  have hzL : z ∈ L := mem_of_pow_pow_mem (hZ z hz) hzm hzp
  exact L.mul_mem hl hzL


theorem eq_one_of_mem_of_isComplement {G : Type} [Group G] {N P : Subgroup G}
    (h : Subgroup.IsComplement (N : Set G) (P : Set G)) {x : G} (hxN : x ∈ N) (hxP : x ∈ P) :
    x = 1 := by
  have hinj : Function.Injective
      (fun z : ↥(N : Set G) × ↥(P : Set G) => (z.1 : G) * (z.2 : G)) := h.1
  have heq : ((⟨⟨x, hxN⟩, ⟨1, P.one_mem⟩⟩ : ↥(N : Set G) × ↥(P : Set G))) =
      ⟨⟨1, N.one_mem⟩, ⟨x, hxP⟩⟩ := by
    apply hinj
    simp
  have := congrArg (fun z : ↥(N : Set G) × ↥(P : Set G) => (z.1 : G)) heq
  simpa using this

theorem pPrime_mem_core_of_central_sylow {p : ℕ} [hp : Fact p.Prime] [Finite Y] {C S : Subgroup Y}
    (hS : IsPGroup p ↥S) (hSC : S ≤ C) (hcent : ∀ s ∈ S, ∀ c ∈ C, s * c = c * s)
    (hall : ∀ R : Subgroup Y, R ≤ C → IsPGroup p ↥R → R ≤ S) :
    ∀ c ∈ C, ¬ p ∣ orderOf c → c ∈ GLAPPrimeCoreOf p C := by
  classical
  let Pc : Subgroup ↥C := S.subgroupOf C
  have hPc : IsPGroup p ↥Pc := by
    intro g
    obtain ⟨k, hk⟩ := hS ⟨(g : ↥Pc).1.1, (g : ↥Pc).2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h1 : (((g : ↥Pc) ^ (p ^ k) : ↥Pc) : ↥C).1 = 1 := by
      have := congrArg (fun z : ↥S => (z : Y)) hk
      simpa using this
    simpa using h1
  let P : Sylow p ↥C := ⟨Pc, hPc, fun {Q} hQ hle => by
    have hR : (Q.map C.subtype : Subgroup Y) ≤ C := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.1 hy
      exact x.2
    have hRp : IsPGroup p ↥(Q.map C.subtype : Subgroup Y) := by
      intro g
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
      obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
      refine ⟨k, ?_⟩
      have h1 : (x : ↥C) ^ (p ^ k) = 1 := by
        have := congrArg (fun z : ↥Q => (z : ↥C)) hk
        simpa using this
      have h2 : ((x : ↥C) : Y) ^ (p ^ k) = 1 := by
        have := congrArg (fun z : ↥C => (z : Y)) h1
        simpa using this
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hxg]
      simpa using h2
    have hRS := hall _ hR hRp
    apply le_antisymm _ hle
    intro x hx
    have hxS : (x : Y) ∈ S := hRS (Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
    exact hxS⟩
  have hnorm : Subgroup.normalizer (P : Set ↥C) ≤ Subgroup.centralizer (P : Set ↥C) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxS : (x : Y) ∈ S := hx
    apply Subtype.ext
    simpa using hcent (x : Y) hxS (g : Y) g.2
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hnorm
  have hNnorm : ((MonoidHom.transferSylow P hnorm).ker).Normal := inferInstance
  have hNcop : Nat.Coprime p (Nat.card (MonoidHom.transferSylow P hnorm).ker) :=
    (Nat.Prime.coprime_iff_not_dvd hp.out).2 (MonoidHom.not_dvd_card_ker_transferSylow P hnorm)
  have hNle : (MonoidHom.transferSylow P hnorm).ker ≤ CFSG.pPrimeCore p ↥C := le_sSup ⟨hNnorm, hNcop⟩
  intro c hc hpc
  let cc : ↥C := ⟨c, hc⟩
  have hmul : (((MonoidHom.transferSylow P hnorm).ker : Subgroup ↥C) : Set ↥C) *
      ((P : Subgroup ↥C) : Set ↥C) = Set.univ := hcomp.mul_eq
  have hmem : cc ∈ (((MonoidHom.transferSylow P hnorm).ker : Subgroup ↥C) : Set ↥C) *
      ((P : Subgroup ↥C) : Set ↥C) := by
    rw [hmul]; exact Set.mem_univ _
  obtain ⟨n, hn, s, hs, hns⟩ := Set.mem_mul.1 hmem
  have hsS : (s : Y) ∈ S := hs
  have hcomm : Commute n s := by
    apply Subtype.ext
    simpa [Commute, SemiconjBy] using (hcent (s : Y) hsS (n : Y) n.2).symm
  have hcordm : orderOf cc = orderOf c := (Subgroup.orderOf_coe cc).symm
  have hm : ¬ p ∣ orderOf cc := by rw [hcordm]; exact hpc
  have hcc : cc ^ orderOf cc = 1 := pow_orderOf_eq_one cc
  have h1 : n ^ orderOf cc * s ^ orderOf cc = 1 := by
    have : (n * s) ^ orderOf cc = 1 := by rw [hns]; exact hcc
    rw [hcomm.mul_pow] at this
    exact this
  have h2 : s ^ orderOf cc = (n ^ orderOf cc)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have h3 : s ^ orderOf cc ∈ (MonoidHom.transferSylow P hnorm).ker := by
    rw [h2]
    exact ((MonoidHom.transferSylow P hnorm).ker).inv_mem
      (((MonoidHom.transferSylow P hnorm).ker).pow_mem hn _)
  have h4 : s ^ orderOf cc ∈ (P : Subgroup ↥C) := (P : Subgroup ↥C).pow_mem hs _
  have hsm : s ^ orderOf cc = 1 := eq_one_of_mem_of_isComplement hcomp h3 h4
  obtain ⟨k, hk⟩ := P.isPGroup' ⟨s, hs⟩
  have hk' : s ^ (p ^ k) = 1 := by
    have := congrArg (fun z : ↥(P : Subgroup ↥C) => (z : ↥C)) hk
    simpa using this
  have hs1 : s = 1 := eq_one_of_pow_eq_one hm hsm hk'
  have hcn : n = cc := by rw [← hns, hs1, mul_one]
  have hnY : (n : Y) = c := congrArg (fun z : ↥C => (z : Y)) hcn
  show c ∈ (CFSG.pPrimeCore p ↥C).map C.subtype
  exact Subgroup.mem_map.2 ⟨n, hNle hn, by rw [Subgroup.coe_subtype]; exact hnY⟩

theorem isPGroup_subgroupOf_of_le {p : ℕ} {A B : Subgroup Y} (hA : IsPGroup p ↥A) (hAB : A ≤ B) :
    IsPGroup p ↥(A.subgroupOf B) := by
  intro g
  obtain ⟨k, hk⟩ := hA ⟨(g : ↥(A.subgroupOf B)).1.1, (g : ↥(A.subgroupOf B)).2⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have := congrArg (fun z : ↥A => (z : Y)) hk
  simpa using this

theorem cz_centralizer {p : ℕ} [hp : Fact p.Prime] [Finite Y] {O Q : Subgroup Y} [hON : O.Normal]
    (hO : ∀ x ∈ O, ¬ p ∣ orderOf x) (hQ : IsPGroup p ↥Q) {h : Y}
    (hh : ∀ q ∈ Q, q⁻¹ * h⁻¹ * q * h ∈ O) :
    ∃ o ∈ O, h * o⁻¹ ∈ Subgroup.centralizer (Q : Set Y) := by
  classical
  have hOtriv : ∀ x ∈ O, ∀ k : ℕ, x ^ (p ^ k) = 1 → x = 1 := fun x hx k hk =>
    eq_one_of_pow_eq_one (hO x hx) (pow_orderOf_eq_one x) hk
  have hQO : ∀ x ∈ Q, x ∈ O → x = 1 := by
    intro x hxQ hxO
    obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
    have hk' : x ^ (p ^ k) = 1 := by
      have := congrArg (fun z : ↥Q => (z : Y)) hk
      simpa using this
    exact hOtriv x hxO k hk'
  set W : Subgroup Y := O ⊔ Q with hWdef
  have hQW : Q ≤ W := le_sup_right
  have hOW : O ≤ W := le_sup_left
  have hWdec : ∀ w ∈ W, ∃ o ∈ O, ∃ q ∈ Q, o * q = w := fun w hw =>
    (Subgroup.mem_sup_of_normal_left (s := O) (t := Q)).1 hw
  let Qw : Subgroup ↥W := Q.subgroupOf W
  have hQw : IsPGroup p ↥Qw := isPGroup_subgroupOf_of_le hQ hQW
  let PQ : Sylow p ↥W := ⟨Qw, hQw, fun {R} hR hle => by
    apply le_antisymm _ hle
    intro r hr
    obtain ⟨o, ho, q, hq, hoq⟩ := hWdec r.1 r.2
    have hqW : q ∈ W := hQW hq
    have hqR : (⟨q, hqW⟩ : ↥W) ∈ R := hle ((Subgroup.mem_subgroupOf).2 hq)
    have hoeq : (⟨o, hOW ho⟩ : ↥W) = r * (⟨q, hqW⟩ : ↥W)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hoq]
      group
    have hoR : (⟨o, hOW ho⟩ : ↥W) ∈ R := by
      rw [hoeq]
      exact R.mul_mem hr (R.inv_mem hqR)
    obtain ⟨k, hk⟩ := hR ⟨⟨o, hOW ho⟩, hoR⟩
    have hk' : o ^ (p ^ k) = 1 := by
      have := congrArg (fun z : ↥W => (z : Y)) (congrArg (fun z : ↥R => (z : ↥W)) hk)
      simpa using this
    have ho1 : o = 1 := hOtriv o ho k hk'
    rw [Subgroup.mem_subgroupOf]
    have hrq : r.1 = q := by
      rw [← hoq, ho1, one_mul]
    rw [hrq]
    exact hq⟩
  let Qh : Subgroup Y := Q.map (MulAut.conj h⁻¹).toMonoidHom
  have hconj : ∀ x : Y, (MulAut.conj h⁻¹).toMonoidHom x = h⁻¹ * x * h := fun x => by
    simp [MulAut.conj_apply]
  have hQhW : Qh ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj]
    have hc : h⁻¹ * x * h = x * (x⁻¹ * h⁻¹ * x * h) := by group
    rw [hc]
    exact W.mul_mem (hQW hx) (hOW (hh x hx))
  have hQh : IsPGroup p ↥Qh := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
    refine ⟨k, ?_⟩
    have h1 : x ^ (p ^ k) = 1 := by
      have := congrArg (fun z : ↥Q => (z : Y)) hk
      simpa using this
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hxg, hconj]
    have h2 : (h⁻¹ * x * h) ^ (p ^ k) = h⁻¹ * x ^ (p ^ k) * h := by
      have h3 := map_pow (MulAut.conj h⁻¹) x (p ^ k)
      simpa only [MulAut.conj_apply, inv_inv] using h3.symm
    rw [h2, h1]
    group
  obtain ⟨Sh, hSh⟩ := IsPGroup.exists_le_sylow (isPGroup_subgroupOf_of_le hQh hQhW)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥W PQ Sh
  obtain ⟨o', ho', q', hq', hdec⟩ := hWdec (g : ↥W).1 (g : ↥W).2
  have hgY : (g : ↥W).1 = o' * q' := hdec.symm
  have hstar : ∀ x ∈ Q, ∃ y ∈ Q, h⁻¹ * x * h = o' * y * o'⁻¹ := by
    intro x hx
    have hyQh : h⁻¹ * x * h ∈ Qh := ⟨x, hx, hconj x⟩
    have hyS : (⟨h⁻¹ * x * h, hQhW hyQh⟩ : ↥W) ∈ Sh :=
      hSh (Subgroup.mem_subgroupOf.2 hyQh)
    have hyS' : (⟨h⁻¹ * x * h, hQhW hyQh⟩ : ↥W) ∈
        ((g • PQ : Sylow p ↥W) : Subgroup ↥W) := by
      rw [hg]; exact hyS
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyS'
    obtain ⟨z, hz, hzeq⟩ := hyS'
    have hzY : (g : ↥W).1 * z.1 * ((g : ↥W).1)⁻¹ = h⁻¹ * x * h := by
      have := congrArg (fun w : ↥W => (w : Y)) hzeq
      simpa [MulAut.smul_def, MulAut.conj_apply] using this
    have hzQ : z.1 ∈ Q := Subgroup.mem_subgroupOf.1 hz
    rw [hgY] at hzY
    refine ⟨q' * z.1 * q'⁻¹, Q.mul_mem (Q.mul_mem hq' hzQ) (Q.inv_mem hq'), ?_⟩
    rw [← hzY]
    group
  refine ⟨o'⁻¹, O.inv_mem ho', ?_⟩
  rw [inv_inv, Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨y, hy, hyeq⟩ := hstar x hx
  have hy2 : y = o'⁻¹ * (h⁻¹ * x * h) * o' := by
    rw [hyeq]; group
  have hmemO : x⁻¹ * y ∈ O := by
    have e : x⁻¹ * y = (x⁻¹ * o'⁻¹ * x) * (x⁻¹ * h⁻¹ * x * h) * o' := by
      rw [hy2]; group
    rw [e]
    exact O.mul_mem (O.mul_mem (by simpa using hON.conj_mem _ (O.inv_mem ho') x⁻¹) (hh x hx)) ho'
  have hone : x⁻¹ * y = 1 := hQO _ (Q.mul_mem (Q.inv_mem hx) hy) hmemO
  have hxy : y = x := by
    calc y = x * (x⁻¹ * y) := by group
      _ = x := by rw [hone, mul_one]
  have hx' : h⁻¹ * x * h = o' * x * o'⁻¹ := by
    rw [hyeq, hxy]
  calc x * (h * o') = h * (h⁻¹ * x * h) * o' := by group
    _ = h * (o' * x * o'⁻¹) * o' := by rw [hx']
    _ = h * o' * x := by group

theorem mem_of_pow_eq_one_of_pow_mem {p : ℕ} [hp : Fact p.Prime] {S : Subgroup Y} {z : Y} {m k : ℕ}
    (hm : ¬ p ∣ m) (hz : z ^ (p ^ k) = 1) (hk : z ^ m ∈ S) : z ∈ S := by
  have hc : IsCoprime ((p ^ k : ℕ) : ℤ) (m : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm)
  obtain ⟨u, v, huv⟩ := hc
  have h1 : (z ^ (p ^ k)) ^ u = 1 := by rw [hz, one_zpow]
  have h2 : (z ^ m) ^ v = z ^ (v * (m : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  have key : z = (z ^ (p ^ k)) ^ u * (z ^ m) ^ v := by
    have h3 : (z ^ (p ^ k)) ^ u = z ^ (u * ((p ^ k : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm]
    rw [h3, h2, ← zpow_add, huv, zpow_one]
  rw [key, h1, one_mul]
  exact S.zpow_mem hk v

@[expose] def layerOf (Y : Type) [Group Y] : Subgroup Y :=
  sSup {K : Subgroup Y | CFSG.Open.IsComponentOf K ⊤}

theorem isComponent_conj_top {K : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤) (g : Y) :
    CFSG.Open.IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
  CFSG.LargeExtraspecial.S5.isComponentOf_map_conj hK (Subgroup.mem_top g)

theorem layerOf_normal : (layerOf Y).Normal := by
  constructor
  intro n hn g
  have key : layerOf Y ≤ (layerOf Y).comap (MulAut.conj g).toMonoidHom := by
    apply sSup_le
    intro K hK
    intro k hk
    have hK' := isComponent_conj_top hK g
    have hmem : (MulAut.conj g).toMonoidHom k ∈ K.map (MulAut.conj g).toMonoidHom :=
      ⟨k, hk, rfl⟩
    exact le_sSup (s := {K : Subgroup Y | CFSG.Open.IsComponentOf K ⊤}) hK' hmem
  exact key hn

theorem comm_of_components [Finite Y] {K K' : Subgroup Y} (hK : CFSG.Open.IsComponentOf K ⊤)
    (hK' : CFSG.Open.IsComponentOf K' ⊤) (hne : K ≠ K') {x y : Y} (hx : x ∈ K) (hy : y ∈ K') :
    x * y = y * x :=
  CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hK hK' hne hx hy

theorem le_glaPPrimeCoreOf_of_normal' {p : ℕ} [Fact p.Prime] {N K : Subgroup Y} (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set Y)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ GLAPPrimeCoreOf p K := by
  have hn : (N.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hcard : Nat.Coprime p (Nat.card ↥(N.subgroupOf K)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv]
    exact hcop
  have hle : N.subgroupOf K ≤ CFSG.pPrimeCore p ↥K := le_sSup ⟨hn, hcard⟩
  intro x hx
  have hxK : x ∈ K := hNK hx
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ N.subgroupOf K := Subgroup.mem_subgroupOf.2 hx
  exact Subgroup.mem_map.2 ⟨⟨x, hxK⟩, hle hmem, rfl⟩

theorem isPGroup_of_le' {p : ℕ} {A B : Subgroup Y} (hB : IsPGroup p ↥B) (hAB : A ≤ B) :
    IsPGroup p ↥A := by
  intro g
  obtain ⟨k, hk⟩ := hB ⟨g.1, hAB g.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun z : ↥B => (z : Y)) hk
  simpa using this

theorem glaPPrimeCoreOf_le_self (p : ℕ) (W : Subgroup Y) : GLAPPrimeCoreOf p W ≤ W :=
  Subgroup.map_subtype_le _

theorem coprime_card_glaPPrimeCoreOf {p : ℕ} [Fact p.Prime] [Finite Y] (W : Subgroup Y) :
    Nat.Coprime p (Nat.card (GLAPPrimeCoreOf p W)) := by
  have h := CFSG.pPrimeCore_coprime_card (p := p) (G := ↥W)
  have e : Nat.card (GLAPPrimeCoreOf p W) = Nat.card (CFSG.pPrimeCore p ↥W) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (CFSG.pPrimeCore p ↥W) W.subtype
      W.subtype_injective).symm.toEquiv
  rw [e]
  exact h

theorem le_normalizer_of_conj {S T : Subgroup Y} (h : ∀ w ∈ T, ∀ y ∈ S, w * y * w⁻¹ ∈ S) :
    T ≤ Subgroup.normalizer (S : Set Y) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy; exact h w hw y hy
  · intro hy
    have := h w⁻¹ (T.inv_mem hw) _ hy
    have e : w⁻¹ * (w * y * w⁻¹) * w⁻¹⁻¹ = y := by group
    rw [e] at this
    exact this

theorem le_normalizer_glaPPrimeCoreOf (p : ℕ) (W : Subgroup Y) :
    W ≤ Subgroup.normalizer (GLAPPrimeCoreOf p W : Set Y) :=
  fun w hw => CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p W
    (Subgroup.le_normalizer hw)

theorem core_inf_sup_le {p : ℕ} [hp : Fact p.Prime] [Finite Y] {L : Subgroup Y} [hL : L.Normal]
    (W : Subgroup Y) :
    GLAPPrimeCoreOf p (W ⊓ (L ⊔ GLAPPrimeCoreOf p W)) ≤ GLAPPrimeCoreOf p W := by
  set Z := GLAPPrimeCoreOf p W with hZ
  set C := W ⊓ (L ⊔ Z) with hC
  set N := GLAPPrimeCoreOf p C with hN
  have hZW : Z ≤ W := glaPPrimeCoreOf_le_self p W
  have hZC : Z ≤ C := le_inf hZW le_sup_right
  have hCW : C ≤ W := inf_le_left
  have hWZ : W ≤ Subgroup.normalizer (Z : Set Y) := le_normalizer_glaPPrimeCoreOf p W
  have hZN : Z ≤ N := le_glaPPrimeCoreOf_of_normal' hZC (hCW.trans hWZ)
    (coprime_card_glaPPrimeCoreOf W)
  have hNC : N ≤ C := glaPPrimeCoreOf_le_self p C
  have hCN : C ≤ Subgroup.normalizer (N : Set Y) := le_normalizer_glaPPrimeCoreOf p C
  set A := L ⊓ W with hA
  have hAW : A ≤ W := inf_le_right
  have hAC : A ≤ C := le_inf hAW ((inf_le_left : L ⊓ W ≤ L).trans le_sup_left)
  have hWA : W ≤ Subgroup.normalizer (A : Set Y) := by
    apply le_normalizer_of_conj
    intro w hw y hy
    exact ⟨hL.conj_mem y hy.1 w, W.mul_mem (W.mul_mem hw hy.2) (W.inv_mem hw)⟩
  have hNA_card : Nat.Coprime p (Nat.card ↥(N ⊓ A)) := by
    have e1 : Nat.card ↥(N ⊓ A) = Nat.card ↥((N ⊓ A).subgroupOf N) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : N ⊓ A ≤ N)).symm.toEquiv
    have hdvd : Nat.card ↥(N ⊓ A) ∣ Nat.card ↥N := by
      rw [e1]; exact Subgroup.card_subgroup_dvd_card _
    exact Nat.Coprime.coprime_dvd_right hdvd (coprime_card_glaPPrimeCoreOf C)
  have hOA : GLAPPrimeCoreOf p A ≤ Z := by
    apply le_glaPPrimeCoreOf_of_normal' ((glaPPrimeCoreOf_le_self p A).trans hAW)
    · exact hWA.trans (CFSG.LocalAnalysis.GLTheoremA.normalizer_le_normalizer_glaPPrimeCoreOf p A)
    · exact coprime_card_glaPPrimeCoreOf A
  have hNAO : N ⊓ A ≤ GLAPPrimeCoreOf p A := by
    apply le_glaPPrimeCoreOf_of_normal' (inf_le_right : N ⊓ A ≤ A)
    · apply le_normalizer_of_conj
      intro w hw y hy
      exact ⟨(Subgroup.mem_normalizer_iff.1 (hCN (hAC hw)) y).1 hy.1,
        (Subgroup.mem_normalizer_iff.1 (hWA (hAW hw)) y).1 hy.2⟩
    · exact hNA_card
  intro n hn
  have hnC : n ∈ C := hNC hn
  obtain ⟨l, hl, z, hz, hlz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := L) (t := Z)).1 hnC.2
  have hzN : z ∈ N := hZN hz
  have hlN : l ∈ N := by
    have : l = n * z⁻¹ := by rw [← hlz]; group
    rw [this]; exact N.mul_mem hn (N.inv_mem hzN)
  have hlW : l ∈ W := by
    have : l = n * z⁻¹ := by rw [← hlz]; group
    rw [this]; exact W.mul_mem hnC.1 (W.inv_mem (hZW hz))
  have hlZ : l ∈ Z := hOA (hNAO ⟨hlN, hl, hlW⟩)
  rw [← hlz]
  exact Z.mul_mem hlZ hz

theorem isPGroup_sup_of_commute {p : ℕ} {A B : Subgroup Y} (hA : IsPGroup p ↥A)
    (hB : IsPGroup p ↥B) (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsPGroup p ↥(A ⊔ B) := by
  have hLE : A ≤ Subgroup.normalizer (B : Set Y) := by
    apply le_normalizer_of_conj
    intro w hw y hy
    have e : w * y * w⁻¹ = y := by rw [hc w hw y hy]; group
    rw [e]; exact hy
  have hset : (↑(A ⊔ B) : Set Y) = A * B := Subgroup.coe_mul_of_left_le_normalizer_right A B hLE
  intro g
  have hg : (g : Y) ∈ (↑(A ⊔ B) : Set Y) := g.2
  rw [hset] at hg
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hg
  obtain ⟨i, hi⟩ := hA ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hB ⟨b, hb⟩
  refine ⟨i + j, Subtype.ext ?_⟩
  have hab' : (g : Y) = a * b := hab.symm
  have hcomm : Commute a b := hc a ha b hb
  have hai : a ^ (p ^ (i + j)) = 1 := by
    have h1 : a ^ (p ^ (i + j)) = (a ^ (p ^ i)) ^ (p ^ j) := by
      rw [← pow_mul, pow_add]
    rw [h1]
    have := congrArg (fun z : ↥A => (z : Y)) hi
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [this, one_pow]
  have hbj : b ^ (p ^ (i + j)) = 1 := by
    have h1 : b ^ (p ^ (i + j)) = (b ^ (p ^ j)) ^ (p ^ i) := by
      rw [← pow_mul, pow_add, mul_comm]
    rw [h1]
    have := congrArg (fun z : ↥B => (z : Y)) hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [this, one_pow]
  simp only [Subgroup.coe_pow, Subgroup.coe_one]
  rw [hab', hcomm.mul_pow, hai, hbj, one_mul]

theorem card_sup_mul_card_inf [Finite Y] {A B : Subgroup Y}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  classical
  let φ : ↥A × ↥B →* Y :=
    { toFun := fun x => (x.1 : Y) * (x.2 : Y)
      map_one' := by simp
      map_mul' := by
        intro x y
        have hyx : (y.1 : Y) * (x.2 : Y) = (x.2 : Y) * (y.1 : Y) :=
          hAB (y.1 : Y) y.1.2 (x.2 : Y) x.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc (x.1 : Y) * (y.1 : Y) * ((x.2 : Y) * (y.2 : Y))
            = (x.1 : Y) * ((y.1 : Y) * (x.2 : Y)) * (y.2 : Y) := by group
          _ = (x.1 : Y) * ((x.2 : Y) * (y.1 : Y)) * (y.2 : Y) := by rw [hyx]
          _ = (x.1 : Y) * (x.2 : Y) * ((y.1 : Y) * (y.2 : Y)) := by group }
  have hLE : A ≤ Subgroup.normalizer (B : Set Y) := by
    apply le_normalizer_of_conj
    intro w hw y hy
    have e : w * y * w⁻¹ = y := by rw [hAB w hw y hy]; group
    rw [e]; exact hy
  have hset : (↑(A ⊔ B) : Set Y) = (A : Set Y) * (B : Set Y) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A B hLE
  have hrange : φ.range = A ⊔ B := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hmem : (x.1 : Y) * (x.2 : Y) ∈ (↑(A ⊔ B) : Set Y) := by
        rw [hset]; exact Set.mul_mem_mul x.1.2 x.2.2
      exact hmem
    · intro hy
      have hy' : y ∈ (↑(A ⊔ B) : Set Y) := hy
      rw [hset] at hy'
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hy'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), by simpa [φ] using hab⟩
  have hfst : ∀ x : ↥φ.ker, ((x : ↥A × ↥B).1 : Y) ∈ A ⊓ B := by
    intro x
    obtain ⟨⟨a, b⟩, hx⟩ := x
    have hx' : (a : Y) * (b : Y) = 1 := hx
    have hinv : (a : Y) = (b : Y)⁻¹ := eq_inv_of_mul_eq_one_left hx'
    refine ⟨a.2, ?_⟩
    rw [hinv]; exact B.inv_mem b.2
  have hker : Nat.card ↥φ.ker = Nat.card ↥(A ⊓ B) := by
    apply Nat.card_congr
    refine
      { toFun := fun x => ⟨((x : ↥A × ↥B).1 : Y), hfst x⟩
        invFun := fun c => ⟨((⟨(c : Y), (Subgroup.mem_inf.1 c.2).1⟩ : ↥A),
            (⟨(c : Y)⁻¹, B.inv_mem (Subgroup.mem_inf.1 c.2).2⟩ : ↥B)), by
              rw [MonoidHom.mem_ker]
              show (c : Y) * (c : Y)⁻¹ = 1
              group⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro x
      obtain ⟨⟨a, b⟩, hx⟩ := x
      have hx' : (a : Y) * (b : Y) = 1 := hx
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext; rfl
      · apply Subtype.ext
        exact (eq_inv_of_mul_eq_one_right hx').symm
    · intro c
      apply Subtype.ext
      rfl
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
        rw [hrange, hker]
    _ = Nat.card ((↥A × ↥B) ⧸ φ.ker) * Nat.card ↥φ.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    _ = Nat.card (↥A × ↥B) := (Subgroup.card_eq_card_quotient_mul_card_subgroup _).symm
    _ = Nat.card ↥A * Nat.card ↥B := Nat.card_prod _ _

theorem sylow_inter_normal {p : ℕ} [hp : Fact p.Prime] [Finite Y] {L N Q : Subgroup Y}
    (hQ : IsSylowIn p L Q) (hNL : N ≤ L) (hNn : ∀ g ∈ L, ∀ x ∈ N, g * x * g⁻¹ ∈ N)
    (T : Subgroup Y) (hTN : T ≤ N) (hTp : IsPGroup p ↥T) (hPT : Q ⊓ N ≤ T) : T = Q ⊓ N := by
  classical
  let M : Subgroup Y := Q ⊔ N
  have hM : M ≤ L := sup_le hQ.1 hNL
  have hQM : IsPGroup p ↥(Q.subgroupOf M) := isPGroup_subgroupOf_of_le hQ.2.1 le_sup_left
  let QM : Sylow p ↥M := ⟨Q.subgroupOf M, hQM, fun {R} hR hle => by
    have hR' : IsPGroup p ↥(R.map M.subtype) := by
      intro g
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
      obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
      refine ⟨k, Subtype.ext ?_⟩
      have := congrArg (fun z : ↥R => (z : ↥M)) hk
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
      rw [← hxg]
      have h2 := congrArg (fun z : ↥M => (z : Y)) this
      simpa using h2
    have hRQ : (R.map M.subtype) ≤ L := fun y hy => hM (by
      obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.1 hy
      exact x.2)
    have hQR : Q ≤ R.map M.subtype := by
      intro q hq
      have hqM : q ∈ M := Subgroup.mem_sup_left hq
      have hmem : (⟨q, hqM⟩ : ↥M) ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.2 hq
      have := hle hmem
      exact Subgroup.mem_map.2 ⟨⟨q, hqM⟩, this, rfl⟩
    have hRQeq : R.map M.subtype = Q := hQ.2.2 _ hRQ hR' hQR
    apply le_antisymm
    · intro r hr
      have : (r : Y) ∈ Q := by
        rw [← hRQeq]; exact Subgroup.mem_map.2 ⟨r, hr, rfl⟩
      exact (Subgroup.mem_subgroupOf).2 this
    · exact hle⟩
  have hTM : T ≤ M := hTN.trans le_sup_right
  have hTm : IsPGroup p ↥(T.subgroupOf M) := isPGroup_subgroupOf_of_le hTp hTM
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hTm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥M QM S
  have hgL : (g : Y) ∈ L := hM g.2
  have key : ∀ t ∈ T, ∃ z ∈ Q, (g : Y) * z * (g : Y)⁻¹ = t := by
    intro t ht
    have htM : t ∈ M := hTM ht
    have hyS' : (⟨t, htM⟩ : ↥M) ∈ ((g • QM : Sylow p ↥M) : Subgroup ↥M) := by
      rw [hg]; exact hS ((Subgroup.mem_subgroupOf).2 ht)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hyS'
    obtain ⟨z, hz, hzeq⟩ := hyS'
    refine ⟨(z : ↥M), (Subgroup.mem_subgroupOf).1 hz, ?_⟩
    have := congrArg (fun w : ↥M => (w : Y)) hzeq
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  let T' : Subgroup Y := T.map (MulAut.conj (g : Y)⁻¹).toMonoidHom
  have hT'sub : T' ≤ Q ⊓ N := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨z, hz, hzt⟩ := key t ht
    have e : (MulAut.conj (g : Y)⁻¹).toMonoidHom t = z := by
      rw [← hzt]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [e]
    refine ⟨hz, ?_⟩
    have hgi : (g : Y)⁻¹ ∈ L := L.inv_mem hgL
    have := hNn _ hgi t (hTN ht)
    have e2 : (g : Y)⁻¹ * t * ((g : Y)⁻¹)⁻¹ = z := by
      rw [← hzt]; simp [mul_assoc]
    rw [← e2]; exact this
  have hcardT' : Nat.card ↥T' = Nat.card ↥T :=
    Subgroup.card_map_of_injective (f := (MulAut.conj (g : Y)⁻¹).toMonoidHom) (MulAut.conj (g : Y)⁻¹).injective
  have hle1 : Nat.card ↥T ≤ Nat.card ↥(Q ⊓ N) := by
    rw [← hcardT']
    exact Subgroup.card_le_of_le hT'sub
  exact (Subgroup.eq_of_le_of_card_ge hPT hle1).symm

theorem exists_card_eq_mul_of_maximal {p : ℕ} [hp : Fact p.Prime] [Finite Y] {N P : Subgroup Y}
    (hPN : P ≤ N) (hP : IsPGroup p ↥P)
    (hmax : ∀ T : Subgroup Y, T ≤ N → IsPGroup p ↥T → P ≤ T → T = P) :
    ∃ m : ℕ, ¬ p ∣ m ∧ Nat.card ↥N = Nat.card ↥P * m := by
  let PN : Sylow p ↥N := ⟨P.subgroupOf N, isPGroup_subgroupOf_of_le hP hPN, fun {R} hR hle => by
    have hR' : IsPGroup p ↥(R.map N.subtype) := by
      intro g
      obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
      obtain ⟨k, hk⟩ := hR ⟨x, hx⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : (x : ↥N) ^ (p ^ k) = 1 := by
        have := congrArg (fun z : ↥R => (z : ↥N)) hk
        simpa using this
      have h2 : ((x : ↥N) : Y) ^ (p ^ k) = 1 := by
        have := congrArg (fun z : ↥N => (z : Y)) h1
        simpa using this
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      rw [← hxg]
      simpa using h2
    have hRN : (R.map N.subtype) ≤ N := fun y hy => by
      obtain ⟨x, _, rfl⟩ := Subgroup.mem_map.1 hy
      exact x.2
    have hPR : P ≤ R.map N.subtype := by
      intro q hq
      have hmem : (⟨q, hPN hq⟩ : ↥N) ∈ P.subgroupOf N := Subgroup.mem_subgroupOf.2 hq
      exact Subgroup.mem_map.2 ⟨⟨q, hPN hq⟩, hle hmem, rfl⟩
    have hRPeq : R.map N.subtype = P := hmax _ hRN hR' hPR
    apply le_antisymm
    · intro r hr
      have : (r : Y) ∈ P := by
        rw [← hRPeq]; exact Subgroup.mem_map.2 ⟨r, hr, rfl⟩
      exact Subgroup.mem_subgroupOf.2 this
    · exact hle⟩
  refine ⟨PN.index, PN.not_dvd_index, ?_⟩
  have h1 := Subgroup.card_mul_index (H := (PN : Subgroup ↥N))
  have h2 : Nat.card ↥(PN : Subgroup ↥N) = Nat.card ↥P := by
    show Nat.card ↥(P.subgroupOf N) = Nat.card ↥P
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem sylow_factor {p : ℕ} [hp : Fact p.Prime] [Finite Y] {L L0 L1 Q : Subgroup Y}
    (hQ : IsSylowIn p L Q) (hsup : L0 ⊔ L1 = L) (hcomm : ∀ x ∈ L0, ∀ y ∈ L1, x * y = y * x)
    (hL0 : ∀ g ∈ L, ∀ x ∈ L0, g * x * g⁻¹ ∈ L0) (hL1 : ∀ g ∈ L, ∀ x ∈ L1, g * x * g⁻¹ ∈ L1) :
    ∀ q ∈ Q, ∃ q0 ∈ Q, q0 ∈ L0 ∧ ∃ q1 ∈ Q, q1 ∈ L1 ∧ q = q0 * q1 := by
  classical
  have hL0L : L0 ≤ L := hsup ▸ le_sup_left
  have hL1L : L1 ≤ L := hsup ▸ le_sup_right
  have hcomm' : ∀ a ∈ L0, ∀ b ∈ L1, a * b = b * a := fun a ha b hb => hcomm a ha b hb
  have hKL : L0 ⊓ L1 ≤ L := inf_le_left.trans hL0L
  have hKn : ∀ g ∈ L, ∀ x ∈ L0 ⊓ L1, g * x * g⁻¹ ∈ L0 ⊓ L1 := fun g hg x hx =>
    ⟨hL0 g hg x hx.1, hL1 g hg x hx.2⟩
  have hQp := hQ.2.1
  have hP0p : IsPGroup p ↥(Q ⊓ L0) := isPGroup_of_le' hQp inf_le_left
  have hP1p : IsPGroup p ↥(Q ⊓ L1) := isPGroup_of_le' hQp inf_le_left
  have hPKp : IsPGroup p ↥(Q ⊓ (L0 ⊓ L1)) := isPGroup_of_le' hQp inf_le_left
  obtain ⟨mL, hmL, hLcard⟩ := exists_card_eq_mul_of_maximal hQ.1 hQp hQ.2.2
  obtain ⟨m0, hm0, hL0card⟩ := exists_card_eq_mul_of_maximal (inf_le_right : Q ⊓ L0 ≤ L0) hP0p
    (fun T hT hTp hle => sylow_inter_normal hQ hL0L hL0 T hT hTp hle)
  obtain ⟨m1, hm1, hL1card⟩ := exists_card_eq_mul_of_maximal (inf_le_right : Q ⊓ L1 ≤ L1) hP1p
    (fun T hT hTp hle => sylow_inter_normal hQ hL1L hL1 T hT hTp hle)
  obtain ⟨mK, hmK, hKcard⟩ := exists_card_eq_mul_of_maximal
    (inf_le_right : Q ⊓ (L0 ⊓ L1) ≤ L0 ⊓ L1) hPKp
    (fun T hT hTp hle => sylow_inter_normal hQ hKL hKn T hT hTp hle)
  have hprodL : Nat.card ↥L * Nat.card ↥(L0 ⊓ L1) = Nat.card ↥L0 * Nat.card ↥L1 := by
    have := card_sup_mul_card_inf (Y := Y) (A := L0) (B := L1) hcomm'
    rw [hsup] at this
    exact this
  have hinter : (Q ⊓ L0) ⊓ (Q ⊓ L1) = Q ⊓ (L0 ⊓ L1) := by
    ext x; simp only [Subgroup.mem_inf]; tauto
  have hprodR : Nat.card ↥((Q ⊓ L0) ⊔ (Q ⊓ L1)) * Nat.card ↥(Q ⊓ (L0 ⊓ L1)) =
      Nat.card ↥(Q ⊓ L0) * Nat.card ↥(Q ⊓ L1) := by
    have := card_sup_mul_card_inf (Y := Y) (A := Q ⊓ L0) (B := Q ⊓ L1)
      (fun a ha b hb => hcomm' a ha.2 b hb.2)
    rw [hinter] at this
    exact this
  set R : Subgroup Y := (Q ⊓ L0) ⊔ (Q ⊓ L1) with hRdef
  have hRQ : R ≤ Q := sup_le inf_le_left inf_le_left
  obtain ⟨e, he⟩ : ∃ e : ℕ, Nat.card ↥Q = Nat.card ↥R * e := by
    refine ⟨(R.subgroupOf Q).index, ?_⟩
    have h1 := Subgroup.card_mul_index (H := R.subgroupOf Q)
    have h2 : Nat.card ↥(R.subgroupOf Q) = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRQ).toEquiv
    rw [h2] at h1
    exact h1.symm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
  have hedvd : e ∣ p ^ n := by
    rw [← hn]
    exact ⟨Nat.card ↥R, by rw [he]; ring⟩
  have hkpos : 0 < Nat.card ↥(Q ⊓ (L0 ⊓ L1)) := Nat.card_pos
  have hrpos : 0 < Nat.card ↥R := Nat.card_pos
  have hprodR' : Nat.card ↥R * Nat.card ↥(Q ⊓ (L0 ⊓ L1)) =
      Nat.card ↥(Q ⊓ L0) * Nat.card ↥(Q ⊓ L1) := hprodR
  have harith : e * (mL * mK) = m0 * m1 := by
    have h1 : (Nat.card ↥Q * mL) * (Nat.card ↥(Q ⊓ (L0 ⊓ L1)) * mK) =
        (Nat.card ↥(Q ⊓ L0) * m0) * (Nat.card ↥(Q ⊓ L1) * m1) := by
      rw [← hLcard, ← hKcard, ← hL0card, ← hL1card]; exact hprodL
    have h2 : (Nat.card ↥Q * mL * mK) * Nat.card ↥(Q ⊓ (L0 ⊓ L1)) =
        (m0 * m1 * Nat.card ↥R) * Nat.card ↥(Q ⊓ (L0 ⊓ L1)) := by
      calc (Nat.card ↥Q * mL * mK) * Nat.card ↥(Q ⊓ (L0 ⊓ L1))
          = (Nat.card ↥Q * mL) * (Nat.card ↥(Q ⊓ (L0 ⊓ L1)) * mK) := by ring
        _ = (Nat.card ↥(Q ⊓ L0) * m0) * (Nat.card ↥(Q ⊓ L1) * m1) := h1
        _ = (m0 * m1) * (Nat.card ↥(Q ⊓ L0) * Nat.card ↥(Q ⊓ L1)) := by ring
        _ = (m0 * m1) * (Nat.card ↥R * Nat.card ↥(Q ⊓ (L0 ⊓ L1))) := by rw [hprodR']
        _ = (m0 * m1 * Nat.card ↥R) * Nat.card ↥(Q ⊓ (L0 ⊓ L1)) := by ring
    have h3 : Nat.card ↥Q * mL * mK = m0 * m1 * Nat.card ↥R :=
      Nat.eq_of_mul_eq_mul_right hkpos h2
    rw [he] at h3
    apply Nat.eq_of_mul_eq_mul_right hrpos
    calc e * (mL * mK) * Nat.card ↥R = (Nat.card ↥R * e) * mL * mK := by ring
      _ = m0 * m1 * Nat.card ↥R := h3
  have hecop : ¬ p ∣ e := by
    intro hpe
    have hdiv : p ∣ m0 * m1 := by
      rw [← harith]; exact Dvd.dvd.mul_right hpe _
    rcases (Nat.Prime.dvd_mul hp.out).1 hdiv with h | h
    · exact hm0 h
    · exact hm1 h
  have he1 : e = 1 := by
    obtain ⟨j, _, hej⟩ := (Nat.dvd_prime_pow hp.out).1 hedvd
    rcases Nat.eq_zero_or_pos j with h0 | hjpos
    · rw [hej, h0, pow_zero]
    · exfalso
      apply hecop
      rw [hej]
      exact dvd_pow_self p (by omega)
  have hRQeq : R = Q := by
    apply Subgroup.eq_of_le_of_card_ge hRQ
    rw [he, he1, mul_one]
  intro q hq
  have hqR : q ∈ (↑R : Set Y) := by rw [hRQeq]; exact hq
  have hLE : Q ⊓ L0 ≤ Subgroup.normalizer ((Q ⊓ L1 : Subgroup Y) : Set Y) := by
    apply le_normalizer_of_conj
    intro w hw y hy
    have e' : w * y * w⁻¹ = y := by rw [hcomm' w hw.2 y hy.2]; group
    rw [e']; exact hy
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (Q ⊓ L0) (Q ⊓ L1) hLE
  have hqset : q ∈ (↑R : Set Y) := hqR
  rw [hRdef, hset] at hqset
  obtain ⟨q0, hq0, q1, hq1, hqq⟩ := Set.mem_mul.1 hqset
  exact ⟨q0, hq0.1, hq0.2, q1, hq1.1, hq1.2, hqq.symm⟩

theorem not_dvd_orderOf_of_mem_glaPPrimeCoreOf {p : ℕ} [hp : Fact p.Prime] [Finite Y]
    {W : Subgroup Y} {z : Y} (hz : z ∈ GLAPPrimeCoreOf p W) : ¬ p ∣ orderOf z := by
  intro hpz
  have hdvd : orderOf (⟨z, hz⟩ : ↥(GLAPPrimeCoreOf p W)) ∣ Nat.card ↥(GLAPPrimeCoreOf p W) :=
    orderOf_dvd_natCard _
  have h1 : orderOf (⟨z, hz⟩ : ↥(GLAPPrimeCoreOf p W)) = orderOf z := (Subgroup.orderOf_coe _).symm
  rw [h1] at hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 (coprime_card_glaPPrimeCoreOf W) (dvd_trans hpz hdvd)

theorem X_le_of_layer {p : ℕ} [hp : Fact p.Prime] [Finite Y] {C0 X Q : Subgroup Y}
    (hQ : IsSylowIn p (layerOf Y) Q)
    (hZ : GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set Y)) ≤ C0)
    (hXp : ∀ x ∈ X, ¬ p ∣ orderOf x)
    (hXL : X ≤ layerOf Y ⊔ GLAPPrimeCoreOf p (Subgroup.centralizer (Q : Set Y)))
    (hXcomm : ∀ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ → ¬ K ≤ C0 →
      ∀ k ∈ K, ∀ x ∈ X, k * x = x * k) :
    X ≤ C0 := by
  classical
  haveI hLn : (layerOf Y).Normal := layerOf_normal
  let L0 : Subgroup Y := sSup {K : Subgroup Y | CFSG.Open.IsComponentOf K ⊤ ∧ K ≤ C0}
  let L1 : Subgroup Y := sSup {K : Subgroup Y | CFSG.Open.IsComponentOf K ⊤ ∧ ¬ K ≤ C0}
  have hL0C : L0 ≤ C0 := sSup_le (fun K hK => hK.2)
  have hL0le : ∀ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ → K ≤ C0 → K ≤ L0 :=
    fun K hK hKC => le_sSup (s := {K : Subgroup Y | CFSG.Open.IsComponentOf K ⊤ ∧ K ≤ C0})
      ⟨hK, hKC⟩
  have hL1le : ∀ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ → ¬ K ≤ C0 → K ≤ L1 :=
    fun K hK hKC => le_sSup (s := {K : Subgroup Y | CFSG.Open.IsComponentOf K ⊤ ∧ ¬ K ≤ C0})
      ⟨hK, hKC⟩
  have hL0L : L0 ≤ layerOf Y := sSup_le fun K hK => le_sSup (s := {K : Subgroup Y |
    CFSG.Open.IsComponentOf K ⊤}) hK.1
  have hL1L : L1 ≤ layerOf Y := sSup_le fun K hK => le_sSup (s := {K : Subgroup Y |
    CFSG.Open.IsComponentOf K ⊤}) hK.1
  have hsplit : L0 ⊔ L1 = layerOf Y := by
    apply le_antisymm (sup_le hL0L hL1L)
    unfold layerOf
    apply sSup_le
    intro K hK
    by_cases hKC : K ≤ C0
    · exact (hL0le K hK hKC).trans le_sup_left
    · exact (hL1le K hK hKC).trans le_sup_right
  have hK1 : ∀ K : Subgroup Y, (CFSG.Open.IsComponentOf K ⊤ ∧ K ≤ C0) →
      ∀ k ∈ K, ∀ y ∈ L1, k * y = y * k := by
    intro K hK k hk y hy
    have hcent : L1 ≤ Subgroup.centralizer (K : Set Y) := by
      apply sSup_le
      intro K' hK'
      intro y' hy'
      rw [Subgroup.mem_centralizer_iff]
      intro k' hk'
      have hne : K ≠ K' := by
        rintro rfl
        exact hK'.2 hK.2
      exact comm_of_components hK.1 hK'.1 hne hk' hy'
    exact (Subgroup.mem_centralizer_iff.1 (hcent hy)) k hk
  have hcentL0 : L0 ≤ Subgroup.centralizer (L1 : Set Y) := by
    apply sSup_le
    intro K hK
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hK1 K hK k hk y hy).symm
  have hcomm01 : ∀ x ∈ L0, ∀ y ∈ L1, x * y = y * x := by
    intro x hx y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hcentL0 hx)) y hy).symm
  have hJ0 : ∀ j ∈ Subgroup.centralizer (L1 : Set Y), ∀ x ∈ L0, j * x * j⁻¹ ∈ L0 := by
    intro j hj x hx
    have hle : L0 ≤ L0.comap (MulAut.conj j).toMonoidHom := by
      apply sSup_le
      intro K hK
      intro k hk
      rw [Subgroup.mem_comap]
      have hcomp : CFSG.Open.IsComponentOf (K.map (MulAut.conj j).toMonoidHom) ⊤ :=
        isComponent_conj_top hK.1 j
      have hmem : (MulAut.conj j).toMonoidHom k ∈ K.map (MulAut.conj j).toMonoidHom :=
        ⟨k, hk, rfl⟩
      by_cases hK' : K.map (MulAut.conj j).toMonoidHom ≤ C0
      · exact hL0le _ hcomp hK' hmem
      · exfalso
        apply hK'
        intro y hy
        obtain ⟨k', hk', hyk⟩ := Subgroup.mem_map.1 hy
        have hyL1 : y ∈ L1 := hL1le _ hcomp hK' hy
        have hcommj : y * j = j * y := (Subgroup.mem_centralizer_iff.1 hj) y hyL1
        have hyk' : j * k' * j⁻¹ = y := by simpa [MulAut.conj_apply] using hyk
        have hk'y : k' = y := by
          have h2 : j * k' = j * y := by
            calc j * k' = (j * k' * j⁻¹) * j := by group
              _ = y * j := by rw [hyk']
              _ = j * y := hcommj
          exact mul_left_cancel h2
        have hyK : y ∈ K := by rw [← hk'y]; exact hk'
        exact hK.2 hyK
    have := hle hx
    rw [Subgroup.mem_comap] at this
    simpa [MulAut.conj_apply] using this
  have hcompnorm0 : ∀ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ →
      K ≤ Subgroup.normalizer (L0 : Set Y) := by
    intro K hK
    by_cases hKC : K ≤ C0
    · exact (hL0le K hK hKC).trans Subgroup.le_normalizer
    · apply le_normalizer_of_conj
      intro k hk x hx
      have hk1 : k ∈ L1 := hL1le K hK hKC hk
      have e : k * x * k⁻¹ = x := by
        rw [← hcomm01 x hx k hk1]; group
      rw [e]; exact hx
  have hcompnorm1 : ∀ K : Subgroup Y, CFSG.Open.IsComponentOf K ⊤ →
      K ≤ Subgroup.normalizer (L1 : Set Y) := by
    intro K hK
    by_cases hKC : K ≤ C0
    · apply le_normalizer_of_conj
      intro k hk y hy
      have e : k * y * k⁻¹ = y := by
        rw [hK1 K ⟨hK, hKC⟩ k hk y hy]; group
      rw [e]; exact hy
    · exact (hL1le K hK hKC).trans Subgroup.le_normalizer
  have hLnorm0 : ∀ g ∈ layerOf Y, ∀ x ∈ L0, g * x * g⁻¹ ∈ L0 := by
    have hle : layerOf Y ≤ Subgroup.normalizer (L0 : Set Y) := by
      unfold layerOf
      apply sSup_le
      intro K hK
      exact hcompnorm0 K hK
    intro g hg x hx
    exact (Subgroup.mem_normalizer_iff.1 (hle hg) x).1 hx
  have hLnorm1 : ∀ g ∈ layerOf Y, ∀ y ∈ L1, g * y * g⁻¹ ∈ L1 := by
    have hle : layerOf Y ≤ Subgroup.normalizer (L1 : Set Y) := by
      unfold layerOf
      apply sSup_le
      intro K hK
      exact hcompnorm1 K hK
    intro g hg y hy
    exact (Subgroup.mem_normalizer_iff.1 (hle hg) y).1 hy
  have hfac := sylow_factor (p := p) hQ hsplit hcomm01 hLnorm0 hLnorm1
  have hXW : X ≤ Subgroup.centralizer (L1 : Set Y) := by
    have hcent : L1 ≤ Subgroup.centralizer (X : Set Y) := by
      apply sSup_le
      intro K hK
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact (hXcomm K hK.1 hK.2 y hy h hh).symm
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hcent hy)) x hx).symm
  set W : Subgroup Y := Subgroup.centralizer (Q : Set Y) with hWdef
  set Z : Subgroup Y := GLAPPrimeCoreOf p W with hZdef
  have hQL : Q ≤ layerOf Y := hQ.1
  have hZW : Z ≤ W := glaPPrimeCoreOf_le_self p W
  have hWnorm : ∀ w ∈ W, w ∈ Subgroup.normalizer (Z : Set Y) := fun w hw =>
    le_normalizer_glaPPrimeCoreOf p W hw
  have hSp : IsPGroup p ↥(Q ⊓ W) := isPGroup_of_le' hQ.2.1 inf_le_left
  have hSC : Q ⊓ W ≤ W ⊓ (layerOf Y ⊔ Z) :=
    le_inf inf_le_right ((inf_le_left.trans hQL).trans le_sup_left)
  have hcentS : ∀ s ∈ Q ⊓ W, ∀ c ∈ W ⊓ (layerOf Y ⊔ Z), s * c = c * s := by
    intro s hs c hc
    exact (Subgroup.mem_centralizer_iff.1 hc.1) s hs.1
  have hnotdvd : ∀ z ∈ Z, ¬ p ∣ orderOf z := fun z hz => not_dvd_orderOf_of_mem_glaPPrimeCoreOf hz
  have hall : ∀ R : Subgroup Y, R ≤ W ⊓ (layerOf Y ⊔ Z) → IsPGroup p ↥R → R ≤ Q ⊓ W := by
    intro R hR hRp
    have hRW : R ≤ W := hR.trans inf_le_left
    have hRc : ∀ r ∈ R, ∀ q ∈ Q, r * q = q * r := by
      intro r hr q hq
      exact ((Subgroup.mem_centralizer_iff.1 (hRW hr)) q hq).symm
    have hTp : IsPGroup p ↥(R ⊔ Q) := isPGroup_sup_of_commute hRp hQ.2.1 hRc
    have hTL : R ⊔ Q ≤ layerOf Y := by
      apply sup_le
      · intro r hr
        have hrLZ : r ∈ layerOf Y ⊔ Z := (hR.trans inf_le_right) hr
        obtain ⟨k, hk⟩ := hRp ⟨r, hr⟩
        have hk' : r ^ (p ^ k) = 1 := by
          have := congrArg (fun z : ↥R => (z : Y)) hk
          simpa using this
        exact mem_of_pow_eq_one_of_mem_sup hnotdvd hrLZ hk'
      · exact hQL
    have hTQ : R ⊔ Q = Q := hQ.2.2 (R ⊔ Q) hTL hTp le_sup_right
    exact le_inf ((le_sup_left : R ≤ R ⊔ Q).trans hTQ.le) hRW
  have hBurn := pPrime_mem_core_of_central_sylow hSp hSC hcentS hall
  have hBZ : ∀ c ∈ W ⊓ (layerOf Y ⊔ Z), ¬ p ∣ orderOf c → c ∈ Z := fun c hc hpc =>
    core_inf_sup_le (p := p) (L := layerOf Y) W (hBurn c hc hpc)
  intro x hx
  obtain ⟨l, hl, z, hz, hlz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := layerOf Y) (t := Z)).1 (hXL hx)
  have hLE0 : L0 ≤ Subgroup.normalizer (L1 : Set Y) := by
    apply le_normalizer_of_conj
    intro w hw y hy
    have e : w * y * w⁻¹ = y := by rw [hcomm01 w hw y hy]; group
    rw [e]; exact hy
  obtain ⟨l0, hl0, l1, hl1, hl01eq⟩ : ∃ l0 ∈ L0, ∃ l1 ∈ L1, l0 * l1 = l := by
    have hmem : l ∈ (↑(L0 ⊔ L1) : Set Y) := by rw [hsplit]; exact hl
    rw [Subgroup.coe_mul_of_left_le_normalizer_right L0 L1 hLE0] at hmem
    obtain ⟨l0, hl0, l1, hl1, h⟩ := Set.mem_mul.1 hmem
    exact ⟨l0, hl0, l1, hl1, h⟩
  have hxd : x = l0 * (l1 * z) := by
    rw [← mul_assoc, hl01eq, hlz]
  set d : Y := l1 * z with hd
  have hdJ : d ∈ Subgroup.centralizer (L1 : Set Y) := by
    have h1 : l0⁻¹ * x ∈ Subgroup.centralizer (L1 : Set Y) :=
      mul_mem (inv_mem (hcentL0 hl0)) (hXW hx)
    have e : l0⁻¹ * x = d := by rw [hxd]; group
    rw [← e]; exact h1
  have hdL : d ∈ layerOf Y ⊔ Z := by
    have h1 : l0⁻¹ * x ∈ layerOf Y ⊔ Z :=
      mul_mem (inv_mem ((le_sup_left : layerOf Y ≤ layerOf Y ⊔ Z) (hL0L hl0))) (hXL hx)
    have e : l0⁻¹ * x = d := by rw [hxd]; group
    rw [← e]; exact h1
  have hdW : d ∈ W := by
    rw [hWdef, Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨q0, hq0Q, hq0L, q1, hq1Q, hq1L, hqq⟩ := hfac q hq
    have c1 : q1 * d = d * q1 := (Subgroup.mem_centralizer_iff.1 hdJ) q1 hq1L
    have hzq0 : q0 * z = z * q0 := (Subgroup.mem_centralizer_iff.1 (hZW hz)) q0 hq0Q
    have c0 : q0 * d = d * q0 := by
      rw [hd]
      calc q0 * (l1 * z) = (q0 * l1) * z := by group
        _ = (l1 * q0) * z := by rw [hcomm01 q0 hq0L l1 hl1]
        _ = l1 * (q0 * z) := by group
        _ = l1 * (z * q0) := by rw [hzq0]
        _ = l1 * z * q0 := by group
    rw [hqq]
    calc q0 * q1 * d = q0 * (q1 * d) := by group
      _ = q0 * (d * q1) := by rw [c1]
      _ = (q0 * d) * q1 := by group
      _ = (d * q0) * q1 := by rw [c0]
      _ = d * (q0 * q1) := by group
  have hdne : orderOf d ≠ 0 := (orderOf_pos d).ne'
  obtain ⟨e, n', hn', hdiv⟩ := Nat.exists_eq_pow_mul_and_not_dvd hdne p (hp.out.one_lt.ne')
  have hcop : IsCoprime ((p ^ e : ℕ) : ℤ) (n' : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn')
  obtain ⟨u, v, huv⟩ := hcop
  have hdn : d ^ (orderOf d) = 1 := pow_orderOf_eq_one d
  have hba : d ^ (u * ((p ^ e : ℕ) : ℤ)) * d ^ (v * (n' : ℤ)) = d := by
    rw [← zpow_add, huv, zpow_one]
  have hbn : (d ^ (u * ((p ^ e : ℕ) : ℤ))) ^ n' = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have e2 : u * ((p ^ e : ℕ) : ℤ) * (n' : ℤ) = u * (orderOf d : ℤ) := by
      rw [hdiv]; push_cast; ring
    rw [e2, mul_comm, zpow_mul, zpow_natCast, hdn, one_zpow]
  have han : (d ^ (v * (n' : ℤ))) ^ (p ^ e) = 1 := by
    rw [← zpow_natCast, ← zpow_mul]
    have e2 : v * (n' : ℤ) * ((p ^ e : ℕ) : ℤ) = v * (orderOf d : ℤ) := by
      rw [hdiv]; push_cast; ring
    rw [e2, mul_comm, zpow_mul, zpow_natCast, hdn, one_zpow]
  set b : Y := d ^ (u * ((p ^ e : ℕ) : ℤ)) with hbdef
  set a : Y := d ^ (v * (n' : ℤ)) with hadef
  have hdba : b * a = d := hba
  have hbW : b ∈ W := (zpow_mem hdW _)
  have hbL : b ∈ layerOf Y ⊔ Z := zpow_mem hdL _
  have hbnd : ¬ p ∣ orderOf b := by
    intro hpb
    have hdvd : orderOf b ∣ n' := orderOf_dvd_of_pow_eq_one hbn
    exact hn' (dvd_trans hpb hdvd)
  have hbZ : b ∈ Z := hBZ b ⟨hbW, hbL⟩ hbnd
  have haW : a ∈ W := zpow_mem hdW _
  have haL : a ∈ layerOf Y ⊔ Z := zpow_mem hdL _
  have haJ : a ∈ Subgroup.centralizer (L1 : Set Y) := zpow_mem hdJ _
  have hnormM : ∀ y ∈ L0 ⊔ Z, a * y * a⁻¹ ∈ L0 ⊔ Z := by
    have hLa : ∀ y ∈ L0, a * y * a⁻¹ ∈ L0 ⊔ Z := fun y hy => Subgroup.mem_sup_left (hJ0 a haJ y hy)
    have hZa : ∀ y ∈ Z, a * y * a⁻¹ ∈ L0 ⊔ Z := fun y hy =>
      Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hWnorm a haW) y).1 hy)
    have hle : L0 ⊔ Z ≤ (L0 ⊔ Z).comap (MulAut.conj a).toMonoidHom :=
      sup_le (fun y hy => by rw [Subgroup.mem_comap]; simpa [MulAut.conj_apply] using hLa y hy)
        (fun y hy => by rw [Subgroup.mem_comap]; simpa [MulAut.conj_apply] using hZa y hy)
    intro y hy
    have := hle hy
    rw [Subgroup.mem_comap] at this
    simpa [MulAut.conj_apply] using this
  have hm_mem : l0 * b ∈ L0 ⊔ Z := mul_mem (Subgroup.mem_sup_left hl0) (Subgroup.mem_sup_right hbZ)
  have hx_eq2 : x = (l0 * b) * a := by
    rw [hxd, ← hdba, mul_assoc]
  have hxN' : (l0 * b * a) ^ (orderOf x) = 1 := by
    rw [← hx_eq2]; exact pow_orderOf_eq_one x
  obtain ⟨m', hm'M, hm'⟩ := exists_mul_pow_eq hnormM hm_mem (orderOf x)
  have hm'eq : m' * a ^ (orderOf x) = 1 := by rw [← hm']; exact hxN'
  have haN : a ^ (orderOf x) ∈ L0 ⊔ Z := by
    have h1 : a ^ (orderOf x) = m'⁻¹ := eq_inv_of_mul_eq_one_right hm'eq
    rw [h1]; exact inv_mem hm'M
  have haM : a ∈ L0 ⊔ Z :=
    mem_of_pow_eq_one_of_pow_mem (hXp x hx) han haN
  have hxM : x ∈ L0 ⊔ Z := by
    rw [hx_eq2]; exact mul_mem hm_mem haM
  exact (sup_le hL0C hZ) hxM

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma114Layer