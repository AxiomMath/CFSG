module

import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617PConj
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.PlaneAlg
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

structure Cfg (p : ℕ) {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) : Prop where
  prime : p.Prime
  five_le : 5 ≤ p
  sylow : CFSG.ABGLocalTools.IsSylowOf p P ⊤
  x_mem : x ∈ P
  z_mem : z ∈ P
  x_pow : x ^ p = 1
  z_pow : z ^ p = 1
  z_ne_one : z ≠ 1
  z_central : ∀ g ∈ P, g * z = z * g
  center_le : ∀ w ∈ P, (∀ g ∈ P, g * w = w * g) → w ^ p = 1 → w ∈ zpowers z
  rank_cent : ∀ E : Subgroup Y, E ≤ P → IsElemAbelian p E → (∀ e ∈ E, e * x = x * e) →
    Nat.card E ≤ p ^ 2
  core : primeComplementCore (G := Y) p = ⊥
  catalog : CFSG.AGLEmbedding.CatalogSimpleSections Y

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y}

theorem Cfg.isPGroup (h : Cfg p P x z) : IsPGroup p P := h.sylow.isPGroup

theorem Cfg.orderOf_z (h : Cfg p P x z) : orderOf z = p := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact orderOf_eq_prime h.z_pow h.z_ne_one

theorem Cfg.z_mem_of_normal (h : Cfg p P x z) {N : Subgroup Y} (hNP : N ≤ P)
    (hN : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hne : N ≠ ⊥) : z ∈ N := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI : Group.IsNilpotent ↥P := h.isPGroup.isNilpotent
  have hnorm : (N.subgroupOf P).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hN g g.2 n hn⟩
  have hHne : N.subgroupOf P ≠ ⊥ := by
    obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    intro hbot
    apply ht1
    have hmem : (⟨t, hNP t.2⟩ : ↥P) ∈ N.subgroupOf P := t.2
    rw [hbot, mem_bot] at hmem
    have h2 : ((⟨t, hNP t.2⟩ : ↥P) : Y) = ((1 : ↥P) : Y) := congrArg Subtype.val hmem
    exact Subtype.ext h2
  have hW : N.subgroupOf P ⊓ center ↥P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
  set W : Subgroup ↥P := N.subgroupOf P ⊓ center ↥P
  have hWp : IsPGroup p W := h.isPGroup.to_subgroup W
  haveI : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).2 hW
  obtain ⟨m, hm, hmcard⟩ := hWp.nontrivial_iff_card.mp inferInstance
  have hdvdW : p ∣ Nat.card W := hmcard ▸ dvd_pow_self p hm.ne'
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := W) p hdvdW
  set u : Y := ((w : ↥P) : Y)
  have hu_ord : orderOf u = p :=
    (Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe _).trans hw)
  have hup : u ^ p = 1 := by
    rw [← hu_ord]
    exact pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hu_ord
    exact h.prime.one_lt.ne hu_ord
  have huC : ∀ g ∈ P, g * u = u * g := fun g hg =>
    congrArg Subtype.val (mem_center_iff.mp w.2.2 ⟨g, hg⟩)
  have hmem : u ∈ zpowers z := h.center_le u (w : ↥P).2 huC hup
  have heq : zpowers u = zpowers z :=
    zpowers_eq_of_mem_zpowers hup h.z_pow hu1 h.z_ne_one hmem
  have hzu : z ∈ zpowers u := by
    rw [heq]
    exact mem_zpowers z
  have huN : u ∈ N := w.2.1
  exact zpowers_le.mpr huN hzu


universe u

theorem card_le_card_ker_pow {M : Type u} [CommGroup M] [Finite M] (k : ℕ) (φ : M →* M)
    (h : ∀ m, φ^[k] m = 1) : Nat.card M ≤ Nat.card φ.ker ^ k := by
  induction k generalizing M with
  | zero =>
    have hsub : Subsingleton M := ⟨fun a b => by
      have ha : a = 1 := h a
      have hb : b = 1 := h b
      rw [ha, hb]⟩
    have : Nat.card M = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    simp [this]
  | succ k ih =>
    have h1 := Subgroup.card_ker_mul_card_range φ
    set M1 : Subgroup M := φ.range with hM1
    let φ1 : M1 →* M1 := (φ.comp M1.subtype).codRestrict M1 (fun y => ⟨y.1, rfl⟩)
    have hφ1 : ∀ y : M1, ((φ1 y : M1) : M) = φ y := fun _ => rfl
    have hiter : ∀ (j : ℕ) (y : M1), ((φ1^[j] y : M1) : M) = φ^[j] (y : M) := by
      intro j
      induction j with
      | zero => intro y; rfl
      | succ j ihj =>
        intro y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hφ1, ihj]
    have hk : ∀ y : M1, φ1^[k] y = 1 := by
      intro y
      obtain ⟨m, hm⟩ := y.2
      apply Subtype.ext
      rw [hiter, ← hm, ← Function.iterate_succ_apply]
      exact h m
    have ih1 := ih φ1 hk
    have hker : Nat.card φ1.ker ≤ Nat.card φ.ker := by
      have hmem : ∀ x : φ1.ker, ((x : M1) : M) ∈ φ.ker := fun x => by
        have h1 : ((φ1 (x : M1) : M1) : M) = 1 := by rw [MonoidHom.mem_ker.mp x.2]; rfl
        exact MonoidHom.mem_ker.mpr (by rw [← hφ1]; exact h1)
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : M1) : M), hmem x⟩) ?_
      intro x y hxy
      have h' : ((x : M1) : M) = ((y : M1) : M) := by simpa using congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h')
    have hM1' : Nat.card M1 ≤ Nat.card φ.ker ^ k :=
      ih1.trans (Nat.pow_le_pow_left hker k)
    rw [← h1, pow_succ']
    exact Nat.mul_le_mul_left _ hM1'


theorem iterate_div_id_eq_one {M : Type*} [CommGroup M] {p : ℕ} [hp : Fact p.Prime]
    (hM : ∀ a : M, a ^ p = 1) (σ : M →* M) (hσ : ∀ a, σ^[p] a = a) (a : M) :
    (⇑(σ / MonoidHom.id M))^[p] a = 1 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hV : ∀ v : Additive M, p • v = 0 := fun v => by
    rw [← ofMul_toMul v, ← ofMul_pow, hM]; rfl
  haveI : Module (ZMod p) (Additive M) := AddCommGroup.zmodModule hV
  let σ' : Module.End (ZMod p) (Additive M) :=
    AddMonoidHom.toZModLinearMap p (MonoidHom.toAdditive σ)
  have hσ'apply : ∀ v : Additive M, σ' v = Additive.ofMul (σ (Additive.toMul v)) :=
    fun v => rfl
  have hiter : ∀ (k : ℕ) (v : Additive M),
      (σ' ^ k) v = Additive.ofMul (σ^[k] (Additive.toMul v)) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih, hσ'apply, Function.iterate_succ_apply']
      rfl
  have hσ'p : σ' ^ p = 1 := LinearMap.ext fun v => by
    rw [hiter, hσ]; rfl
  have hT : (σ' - 1) ^ p = 0 := by
    have h2 : ((Polynomial.X - 1 : Polynomial (ZMod p)) ^ p) = Polynomial.X ^ p - 1 := by
      rw [sub_pow_char]; simp
    have h3 := congrArg (Polynomial.aeval σ') h2
    simpa [hσ'p] using h3
  have hTiter : ∀ (k : ℕ) (b : M), ((σ' - 1) ^ k) (Additive.ofMul b) =
      Additive.ofMul ((⇑(σ / MonoidHom.id M))^[k] b) := by
    intro k
    induction k with
    | zero => intro b; rfl
    | succ k ih =>
      intro b
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply']
      show σ' (Additive.ofMul _) - Additive.ofMul _ = _
      rw [hσ'apply]
      rfl
  have := congrArg (fun f => f (Additive.ofMul a)) hT
  rw [hTiter] at this
  exact Additive.ofMul.injective this

theorem card_le_card_centralizer_pow (hp : p.Prime) {E : Subgroup Y} (hE : IsElemAbelian p E)
    {x : Y} (hx : x ∈ normalizer (E : Set Y)) (hxp : x ^ p = 1) :
    Nat.card E ≤ Nat.card ↥(E ⊓ centralizer ({x} : Set Y)) ^ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup ↥E := { (inferInstance : Group ↥E) with
    mul_comm := fun a b => hE.1.is_comm.comm a b }
  have hconj : ∀ a : ↥E, x * (a : Y) * x⁻¹ ∈ E := fun a => (mem_normalizer_iff.mp hx a).mp a.2
  let σ : ↥E →* ↥E := MonoidHom.mk' (fun a => ⟨x * a * x⁻¹, hconj a⟩) (fun a b =>
    Subtype.ext (by change x * (a * b : Y) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹); group))
  have hσiter : ∀ (k : ℕ) (a : ↥E), ((σ^[k] a : ↥E) : Y) = x ^ k * a * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [Function.iterate_succ_apply']
      show x * ((σ^[k] a : ↥E) : Y) * x⁻¹ = _
      rw [ih, pow_succ']
      group
  have hσp : ∀ a, σ^[p] a = a := fun a => Subtype.ext (by rw [hσiter, hxp]; group)
  have hpow : ∀ a : ↥E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hE.2 a a.2)
  have hbound := card_le_card_ker_pow p (σ / MonoidHom.id ↥E) (iterate_div_id_eq_one hpow σ hσp)
  have hker : Nat.card (σ / MonoidHom.id ↥E).ker ≤ Nat.card ↥(E ⊓ centralizer ({x} : Set Y)) := by
    have hmem : ∀ m : (σ / MonoidHom.id ↥E).ker,
        ((m : ↥E) : Y) ∈ E ⊓ centralizer ({x} : Set Y) := by
      intro m
      refine ⟨(m : ↥E).2, ?_⟩
      have hm : (σ / MonoidHom.id ↥E) (m : ↥E) = 1 := m.2
      have h1 : σ (m : ↥E) = (m : ↥E) := by
        simpa [MonoidHom.div_apply, div_eq_one] using hm
      have h2 : x * ((m : ↥E) : Y) * x⁻¹ = ((m : ↥E) : Y) := congrArg Subtype.val h1
      show ((m : ↥E) : Y) ∈ centralizer ({x} : Set Y)
      rw [mem_centralizer_singleton_iff]
      symm
      calc x * ((m : ↥E) : Y) = (x * ((m : ↥E) : Y) * x⁻¹) * x := by group
        _ = ((m : ↥E) : Y) * x := by rw [h2]
    refine Nat.card_le_card_of_injective (fun m => ⟨((m : ↥E) : Y), hmem m⟩) ?_
    intro m n hmn
    exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hmn))
  exact hbound.trans (Nat.pow_le_pow_left hker p)


theorem card_mul_le_card_sup {K X : Subgroup Y} (h : K ⊓ X = ⊥) :
    Nat.card K * Nat.card X ≤ Nat.card ↥(K ⊔ X) := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective
    (fun a : K × X => (⟨(a.1 : Y) * (a.2 : Y), Subgroup.mul_mem_sup a.1.2 a.2.2⟩ : ↥(K ⊔ X)))
    ?_
  rintro ⟨a, b⟩ ⟨a', b'⟩ hab
  have h1 : (a : Y) * b = a' * b' := congrArg Subtype.val hab
  have h2 : (a' : Y)⁻¹ * a = (b' : Y) * (b : Y)⁻¹ := by
    calc (a' : Y)⁻¹ * a = (a' : Y)⁻¹ * (a * b) * (b : Y)⁻¹ := by group
      _ = (a' : Y)⁻¹ * (a' * b') * (b : Y)⁻¹ := by rw [h1]
      _ = (b' : Y) * (b : Y)⁻¹ := by group
  have h3 : (a' : Y)⁻¹ * a ∈ K ⊓ X :=
    ⟨K.mul_mem (K.inv_mem a'.2) a.2, h2 ▸ X.mul_mem b'.2 (X.inv_mem b.2)⟩
  rw [h, Subgroup.mem_bot, inv_mul_eq_one] at h3
  have h4 : (b : Y) = b' := by
    rw [← h3] at h1
    exact mul_left_cancel h1
  exact Prod.ext (Subtype.ext h3.symm) (Subtype.ext h4)

theorem isElemAbelian_sup {A B : Subgroup Y} (hA : IsElemAbelian p A) (hB : IsElemAbelian p B)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : IsElemAbelian p (A ⊔ B) := by
  have e : A ⊔ B = ⨆ i : Bool, cond i A B := sup_eq_iSup A B
  have hcomm : ∀ u ∈ A ⊔ B, ∀ v ∈ A ⊔ B, u * v = v * u := by
    intro u hu v hv
    rw [e] at hu hv
    refine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617P.commute_of_iSup (fun i : Bool =>
      cond i A B) ?_ hu hv
    intro i j a ha b hb
    cases i <;> cases j
    · exact congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    · exact (hAB b hb a ha).symm
    · exact hAB a ha b hb
    · exact congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine ⟨⟨⟨fun u v => Subtype.ext (hcomm u u.2 v v.2)⟩⟩, ?_⟩
  intro g hg
  have hg' := hg
  rw [e] at hg'
  refine Subgroup.iSup_induction' (fun i : Bool => cond i A B)
    (C := fun g _ => g ^ p = 1) ?_ (one_pow p) ?_ hg'
  · intro i g hg
    cases i
    · exact hB.2 g hg
    · exact hA.2 g hg
  · intro a b ha hb iha ihb
    have hc : Commute a b := hcomm a (e ▸ ha) b (e ▸ hb)
    rw [hc.mul_pow, iha, ihb, mul_one]


theorem Cfg.card_cent_le (h : Cfg p P x z) {E : Subgroup Y} (hEP : E ≤ P)
    (hE : IsElemAbelian p E) (hxE : x ∉ E) :
    Nat.card ↥(E ⊓ centralizer ({x} : Set Y)) ≤ p := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup Y := E ⊓ centralizer ({x} : Set Y) with hK
  have hxne : x ≠ 1 := fun h1 => hxE (h1 ▸ E.one_mem)
  have hXc : Nat.card (zpowers x) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime h.x_pow hxne]
  have hKX : K ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    by_contra hg1
    have hgE : g ∈ E := hg.1.1
    have hgp : g ^ p = 1 := hE.2 g hgE
    have hzp := zpowers_eq_of_mem_zpowers hgp h.x_pow hg1 hxne hg.2
    apply hxE
    have : x ∈ zpowers g := by rw [hzp]; exact mem_zpowers x
    exact zpowers_le.mpr hgE this
  have hKe : IsElemAbelian p K := CFSG.Open.IsElemAbelian.mono hE inf_le_left
  have hXe : IsElemAbelian p (zpowers x) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1
      (CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one h.x_pow)
  have hKXc : ∀ a ∈ K, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    have hxa : x * a = a * x := (mem_centralizer_singleton_iff.mp ha.2).symm
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hb
    exact ((Commute.zpow_right (show Commute a x from hxa.symm) n).eq)
  have hFe : IsElemAbelian p (K ⊔ zpowers x) := isElemAbelian_sup hKe hXe hKXc
  have hFP : K ⊔ zpowers x ≤ P :=
    sup_le (inf_le_left.trans hEP) (zpowers_le.mpr h.x_mem)
  have hFx : ∀ e ∈ K ⊔ zpowers x, e * x = x * e := fun e he =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨e, he⟩
      ⟨x, Subgroup.mem_sup_right (mem_zpowers x)⟩)
  have hF2 := h.rank_cent _ hFP hFe hFx
  have hcard := card_mul_le_card_sup hKX
  rw [hXc] at hcard
  have h1 : Nat.card K * p ≤ p * p := by
    calc Nat.card K * p ≤ Nat.card ↥(K ⊔ zpowers x) := hcard
      _ ≤ p ^ 2 := hF2
      _ = p * p := by ring
  exact Nat.le_of_mul_le_mul_right h1 hp.pos

theorem Cfg.card_le_of_normalizes (h : Cfg p P x z) {E : Subgroup Y} (hEP : E ≤ P)
    (hE : IsElemAbelian p E) (hx : x ∈ normalizer (E : Set Y)) : Nat.card E ≤ p ^ p := by
  have hp := h.prime
  have h5 := h.five_le
  by_cases hxE : x ∈ E
  · have hc : ∀ e ∈ E, e * x = x * e := fun e he =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨x, hxE⟩)
    calc Nat.card E ≤ p ^ 2 := h.rank_cent E hEP hE hc
      _ ≤ p ^ p := Nat.pow_le_pow_right hp.pos (by omega)
  · calc Nat.card E ≤ Nat.card ↥(E ⊓ centralizer ({x} : Set Y)) ^ p :=
          card_le_card_centralizer_pow hp hE hx h.x_pow
      _ ≤ p ^ p := Nat.pow_le_pow_left (h.card_cent_le hEP hE hxE) p

theorem Cfg.card_le_sq_of_comm (h : Cfg p P x z) {E : Subgroup Y} (hEP : E ≤ P)
    (hE : IsElemAbelian p E) (hcomm : ∀ e ∈ E, x * e * x⁻¹ * e⁻¹ ∈ zpowers z) :
    Nat.card E ≤ p ^ 2 := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hxE : x ∈ E
  · have hc : ∀ e ∈ E, e * x = x * e := fun e he =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨x, hxE⟩)
    exact h.rank_cent E hEP hE hc
  · have hzcent : ∀ w ∈ zpowers z, ∀ g ∈ P, g * w = w * g := by
      intro w hw g hg
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hw
      exact (Commute.zpow_right (show Commute g z from h.z_central g hg) n).eq
    let δ : ↥E →* ↥(zpowers z) := MonoidHom.mk' (fun e => ⟨x * e * x⁻¹ * (e : Y)⁻¹, hcomm e e.2⟩)
      (fun e e' => by
        apply Subtype.ext
        have hc : ((e : Y)) * (x * e' * x⁻¹ * (e' : Y)⁻¹) = (x * e' * x⁻¹ * (e' : Y)⁻¹) * e :=
          hzcent _ (hcomm e' e'.2) e (hEP e.2)
        change x * ((e : Y) * e') * x⁻¹ * ((e : Y) * e')⁻¹ =
          (x * e * x⁻¹ * (e : Y)⁻¹) * (x * e' * x⁻¹ * (e' : Y)⁻¹)
        calc x * ((e : Y) * e') * x⁻¹ * ((e : Y) * e')⁻¹
            = x * e * x⁻¹ * (x * e' * x⁻¹ * (e' : Y)⁻¹) * (e : Y)⁻¹ := by group
          _ = x * e * x⁻¹ * ((e : Y)⁻¹ * ((e : Y) * (x * e' * x⁻¹ * (e' : Y)⁻¹)) * (e : Y)⁻¹) := by
            group
          _ = x * e * x⁻¹ * ((e : Y)⁻¹ * ((x * e' * x⁻¹ * (e' : Y)⁻¹) * e) * (e : Y)⁻¹) := by
            rw [hc]
          _ = (x * e * x⁻¹ * (e : Y)⁻¹) * (x * e' * x⁻¹ * (e' : Y)⁻¹) := by group)
    have h1 := Subgroup.card_ker_mul_card_range δ
    have hker : Nat.card δ.ker ≤ Nat.card ↥(E ⊓ centralizer ({x} : Set Y)) := by
      have hmem : ∀ m : δ.ker, ((m : ↥E) : Y) ∈ E ⊓ centralizer ({x} : Set Y) := by
        intro m
        refine ⟨(m : ↥E).2, ?_⟩
        have hm : δ (m : ↥E) = 1 := m.2
        have h2 : x * ((m : ↥E) : Y) * x⁻¹ * ((m : ↥E) : Y)⁻¹ = 1 := congrArg Subtype.val hm
        show ((m : ↥E) : Y) ∈ centralizer ({x} : Set Y)
        rw [mem_centralizer_singleton_iff]
        symm
        have h3 := mul_inv_eq_one.mp h2
        rw [mul_inv_eq_iff_eq_mul] at h3
        exact h3
      refine Nat.card_le_card_of_injective (fun m => ⟨((m : ↥E) : Y), hmem m⟩) ?_
      intro m n hmn
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hmn))
    have hrange : Nat.card δ.range ≤ p := by
      have : Nat.card δ.range ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_card_group _
      rwa [Nat.card_zpowers, h.orderOf_z] at this
    calc Nat.card E = Nat.card δ.ker * Nat.card δ.range := h1.symm
      _ ≤ p * p := Nat.mul_le_mul (hker.trans (h.card_cent_le hEP hE hxE)) hrange
      _ = p ^ 2 := by ring

theorem Cfg.comm_mem_zpowers (h : Cfg p P x z) {U : Subgroup Y} (hUP : U ≤ P)
    (hUn : ∀ g ∈ P, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hUc : Nat.card U = p ^ 2) :
    ∀ g ∈ P, ∀ u ∈ U, g * u * g⁻¹ * u⁻¹ ∈ zpowers z := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hU1 : U ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hUc
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hzU : z ∈ U := h.z_mem_of_normal hUP hUn hU1
  have hzc : Nat.card (zpowers z) = p := by rw [Nat.card_zpowers, h.orderOf_z]
  have hAU : zpowers z ≤ U := zpowers_le.mpr hzU
  haveI hAn : ((zpowers z).subgroupOf P).Normal := by
    refine Subgroup.normal_of_le_center ?_
    intro a ha
    rw [Subgroup.mem_subgroupOf, mem_zpowers_iff] at ha
    obtain ⟨n, hn⟩ := ha
    rw [Subgroup.mem_center_iff]
    intro t
    apply Subtype.ext
    show (t : Y) * (a : Y) = (a : Y) * t
    rw [← hn]
    exact (Commute.zpow_right (show Commute (t : Y) z from h.z_central t t.2) n).eq
  haveI hCn : (U.subgroupOf P).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hUn g g.2 n hn⟩
  have hAC : (zpowers z).subgroupOf P < U.subgroupOf P := by
    refine lt_of_le_of_ne (fun a ha => hAU ha) fun heq => ?_
    have h1 : Nat.card ((zpowers z).subgroupOf P) = Nat.card U := by
      rw [heq]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAU.trans hUP)).toEquiv, hzc, hUc] at h1
    have : p < p ^ 2 := by nlinarith [hp.one_lt]
    omega
  obtain ⟨b, -, -, -, B, -, hAB, hBC, -, -, hcomm⟩ :=
    CFSG.SectionRank.Ccomm.exists_central_extension h.isPGroup hAC
  have hBeq : B = U.subgroupOf P := by
    refine Subgroup.eq_of_le_of_card_ge hBC ?_
    have hcardC : Nat.card (U.subgroupOf P) = p ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUP).toEquiv, hUc]
    obtain ⟨j, hj⟩ := (h.isPGroup.to_subgroup B).exists_card_eq
    have hlt : Nat.card ((zpowers z).subgroupOf P) < Nat.card B := Subgroup.card_lt_of_lt hAB
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hAU.trans hUP)).toEquiv, hzc, hj] at hlt
    have hj2 : 2 ≤ j := by
      by_contra hj'
      have hj1 : j ≤ 1 := by omega
      have h2 : p ^ j ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hj1
      rw [pow_one] at h2
      omega
    rw [hcardC, hj]
    exact Nat.pow_le_pow_right hp.pos hj2
  intro g hg u hu
  have hmem : (⟨u, hUP hu⟩ : ↥P) ∈ B := by rw [hBeq]; exact hu
  have h1 := hcomm _ hmem ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : g * u * g⁻¹ * u⁻¹ = (u * g * u⁻¹ * g⁻¹)⁻¹ := by group
  rw [h2]
  exact (zpowers z).inv_mem (by simpa [commutatorElement_def] using h1)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
