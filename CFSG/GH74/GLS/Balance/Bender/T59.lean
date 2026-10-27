module

public import CFSG.GH74.GLS.Balance.Bender.OpStarP
public import CFSG.GH74.GLS.Balance.Bender.Aux2

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance.BenderExt
open scoped commutatorElement

theorem t59_frattini {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {X N P : Subgroup G}
    (hNX : N ≤ X) (hNn : (N.subgroupOf X).Normal) (hP : IsSylowIn p P N) :
    X ≤ N ⊔ (X ⊓ normalizer (P : Set G)) := by
  intro x hx
  have hxN : x ∈ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hNX hx
  have hP' : IsSylowIn p (P.map (MulAut.conj x).toMonoidHom) (N.map (MulAut.conj x).toMonoidHom) :=
    IsSylowIn.map (MulAut.conj x).injective hP
  have hNmap : N.map (MulAut.conj x).toMonoidHom = N := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.mp hxN y).mp hy
    · intro hz
      refine ⟨x⁻¹ * z * x, ?_, ?_⟩
      · have h1 := (mem_normalizer_iff.mp hxN (x⁻¹ * z * x)).mpr (by simpa [mul_assoc] using hz)
        exact h1
      · simp [MulAut.conj_apply, mul_assoc]
  rw [hNmap] at hP'
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn p hP
  obtain ⟨S', hS'⟩ := exists_sylow_of_isSylowIn p hP'
  obtain ⟨k, hk, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj ⟨S, hS⟩ ⟨S', hS'⟩
  have hg : k⁻¹ * x ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff]
    intro w
    have h1 : x * w * x⁻¹ ∈ P.map (MulAut.conj x).toMonoidHom ↔ w ∈ P := by
      constructor
      · rintro ⟨y, hy, hyw⟩
        have : y = w := by
          have h2 : x * y * x⁻¹ = x * w * x⁻¹ := hyw
          simpa using h2
        rw [← this]; exact hy
      · intro hw
        exact ⟨w, hw, rfl⟩
    have h2 := hconj (x * w * x⁻¹)
    rw [h1] at h2
    rw [h2]
    have : k⁻¹ * (x * w * x⁻¹) * k = k⁻¹ * x * w * (k⁻¹ * x)⁻¹ := by group
    rw [this]
  have hgX : k⁻¹ * x ∈ X := X.mul_mem (X.inv_mem (hNX hk)) hx
  have hkx : x = k * (k⁻¹ * x) := by group
  rw [hkx]
  exact Subgroup.mul_mem_sup hk ⟨hgX, hg⟩



theorem t59_le_sup_sylow {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {O N P : Subgroup G}
    (hOn : (O.subgroupOf N).Normal) (hpow : ∀ n ∈ N, ∃ k : ℕ, n ^ p ^ k ∈ O)
    (hP : IsSylowIn p P N) : N ≤ O ⊔ P := by
  set O' : Subgroup ↥N := O.subgroupOf N with hO'
  set P' : Subgroup ↥N := P.subgroupOf N with hP'
  have hPN : P ≤ N := hP.1
  have hcardP : Nat.card P' = Nat.card P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPN).toEquiv
  have hP's : IsSylowIn p P' (⊤ : Subgroup ↥N) := by
    refine ⟨le_top, hP.2.1.comap_of_injective N.subtype N.subtype_injective, fun S _ hS => ?_⟩
    have h1 : Nat.card (S.map N.subtype) ≤ Nat.card P :=
      hP.2.2 _ (Subgroup.map_subtype_le S) (hS.map N.subtype)
    have h2 : Nat.card (S.map N.subtype) = Nat.card S := Subgroup.card_map_of_injective N.subtype_injective
    rw [hcardP]
    omega
  have hmap := isSylowIn_map_surjective (p := p) (QuotientGroup.mk' O') (QuotientGroup.mk'_surjective O') hP's
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O')] at hmap
  have hQp : IsPGroup p (↥N ⧸ O') := by
    intro z
    obtain ⟨⟨n, hn⟩, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk⟩ := hpow n hn
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have htop : IsPGroup p ↥(⊤ : Subgroup (↥N ⧸ O')) :=
    hQp.of_injective (⊤ : Subgroup (↥N ⧸ O')).subtype (Subgroup.subtype_injective _)
  have hcard : Nat.card ↥(⊤ : Subgroup (↥N ⧸ O')) ≤ Nat.card ↥(P'.map (QuotientGroup.mk' O')) :=
    hmap.2.2 ⊤ le_rfl htop
  have hPtop : P'.map (QuotientGroup.mk' O') = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top hcard
  intro n hn
  have h1 : (QuotientGroup.mk' O') ⟨n, hn⟩ ∈ P'.map (QuotientGroup.mk' O') := by
    rw [hPtop]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxn⟩ := h1
  have h2 : x⁻¹ * ⟨n, hn⟩ ∈ O' := QuotientGroup.eq.mp hxn
  have h3 : (x : G)⁻¹ * n ∈ O := h2
  have h4 : n = (x : G) * ((x : G)⁻¹ * n) := by group
  rw [h4, sup_comm]
  exact Subgroup.mul_mem_sup hx h3



theorem t59_mul_pow_mem {G : Type*} [Group G] {A : Subgroup G} {a b : G} (ha : a ∈ A)
    (hb : b ∈ normalizer (A : Set G)) (j : ℕ) : ∃ a' ∈ A, (a * b) ^ j = a' * b ^ j := by
  induction j with
  | zero => exact ⟨1, A.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨a', ha', h⟩ := ih
    have hbj : b ^ j ∈ normalizer (A : Set G) := Subgroup.pow_mem _ hb j
    have hc : b ^ j * a * (b ^ j)⁻¹ ∈ A := (mem_normalizer_iff.mp hbj a).mp ha
    refine ⟨a' * (b ^ j * a * (b ^ j)⁻¹), A.mul_mem ha' hc, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem t59_core {p : ℕ} [Fact p.Prime] (h53 : BenderL53 p) (h56 : BenderL56 p)
    {G : Type} [Group G] [Finite G] {X P M : Subgroup G}
    (hP : IsSylowIn p P (OpStarP p X))
    (hMX : M ≤ X) (hNM : OpStarP p X ≤ M) (hMn : (M.subgroupOf X).Normal)
    (hMW : M ≤ OpStarP p X ⊔ (X ⊓ centralizer (P : Set G)))
    [hNnM : ((OpStarP p X).subgroupOf M).Normal]
    (hquot : IsPStar p (↥M ⧸ (OpStarP p X).subgroupOf M)) :
    oResOf p M ≤ OpStar p X := by
  set O : Subgroup G := OpStar p X with hO
  set N : Subgroup G := OpStarP p X with hN
  set D : Subgroup G := M ⊓ centralizer (P : Set G) with hD
  have hNX : N ≤ X := opStarP_le p X
  have hXN : X ≤ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hNX
  have hOe : oResOf p N = O := oResOf_opStarP h56 X
  have hON : O ≤ N := opStar_le_opStarP p X
  have hPN : P ≤ N := hP.1
  have hXO : X ≤ normalizer (O : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf (opStar_le p X)
  have hOnN : (O.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mpr (hNX.trans hXO)
  have hNOP : N ≤ O ⊔ P := t59_le_sup_sylow hOnN (fun n hn => opStarP_pow_mem p X hn) hP
  have hMND : ∀ m ∈ M, ∃ n ∈ N, ∃ c ∈ D, n * c = m := by
    intro m hm
    obtain ⟨n, hn, c, hc, hnc⟩ := (mem_sup_of_le_normalizer (inf_le_left.trans hXN)).1 (hMW hm)
    refine ⟨n, hn, c, Subgroup.mem_inf.mpr ⟨?_, hc.2⟩, hnc⟩
    have : c = n⁻¹ * m := by rw [← hnc]; group
    rw [this]
    exact M.mul_mem (M.inv_mem (hNM hn)) hm
  set E : Subgroup G := O ⊔ D with hE
  have hDO : D ≤ normalizer (O : Set G) := fun d hd => hXO (hMX hd.1)
  have hfwd : ∀ x ∈ P, ∀ w ∈ E, x * w * x⁻¹ ∈ E := by
    intro x hx w hw
    obtain ⟨o, ho, d, hd, rfl⟩ := (mem_sup_of_le_normalizer hDO).1 hw
    have hxd : x * d = d * x := mem_centralizer_iff.mp hd.2 x hx
    have hxo : x * o * x⁻¹ ∈ O := (mem_normalizer_iff.mp (hXO (hNX (hPN hx))) o).mp ho
    have hd' : x * d * x⁻¹ = d := by rw [hxd]; group
    have : x * (o * d) * x⁻¹ = (x * o * x⁻¹) * (x * d * x⁻¹) := by group
    rw [this, hd']
    exact Subgroup.mul_mem_sup hxo hd
  have hPE : P ≤ normalizer (E : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro w
    refine ⟨hfwd x hx w, fun hw => ?_⟩
    have := hfwd x⁻¹ (P.inv_mem hx) _ hw
    simpa [mul_assoc] using this
  have hOE : O ≤ normalizer (E : Set G) := fun o ho => Subgroup.le_normalizer (Subgroup.mem_sup_left ho)
  have hpelt : ∀ m ∈ M, Nat.Coprime (orderOf m) p → m ∈ E := by
    intro m hm hcop
    obtain ⟨n, hn, c, hc, hnc⟩ := hMND m hm
    obtain ⟨o, ho, x, hx, hox⟩ :=
      (mem_sup_of_le_normalizer (hPN.trans (hNX.trans hXO))).1 (hNOP hn)
    have hxc : x * c = c * x := mem_centralizer_iff.mp hc.2 x hx
    have hm' : m = (o * c) * x := by
      rw [← hnc, ← hox, mul_assoc, hxc, ← mul_assoc]
    have he : o * c ∈ E := Subgroup.mul_mem_sup ho hc
    obtain ⟨k, hk⟩ := hP.2.1 ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨a', ha', hpow⟩ := t59_mul_pow_mem he (hPE hx) (p ^ k)
    have hmpow : m ^ p ^ k ∈ E := by
      rw [hm', hpow, hxk, mul_one]; exact ha'
    exact mem_of_pow_mem_of_coprime (Nat.Coprime.pow_left k hcop.symm) hmpow
  have hres : oResOf p M ≤ oResOf p N ⊔ (M ⊓ centralizer (P : Set G)) := by
    rw [hOe]; exact oResOf_le_of hpelt
  have hNp : IsPStar p ↥(oResOf p N) := by rw [hOe]; exact isPStar_opStar h56 X
  have hM53 : IsPStar p ↥(oResOf p M) := h53 G M N P hNM hP hquot hNp hres
  have hRX : oResOf p M ≤ X := (oResOf_le p M).trans hMX
  have hRn : ((oResOf p M).subgroupOf X).Normal := by
    refine ⟨fun r hr y => ?_⟩
    have hyM : (y : G) ∈ normalizer (M : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hMX y.2
    exact conj_mem_oResOf hyM hr
  exact le_opStar hRX hRn hM53


theorem bender_t59 {p : ℕ} [Fact p.Prime] (h52iii : BenderL52iii p) (h53 : BenderL53 p)
    (h56 : BenderL56 p) : BenderT59 p := by
  intro G _ _ X P hP
  have hp : p.Prime := Fact.out
  by_contra hC
  set N : Subgroup G := OpStarP p X with hN
  set C : Subgroup G := X ⊓ centralizer (P : Set G) with hCdef
  have hNX : N ≤ X := opStarP_le p X
  have hNn : (N.subgroupOf X).Normal := opStarP_normal p X
  have hXN : X ≤ normalizer (N : Set G) := Subgroup.le_normalizer_of_normal_subgroupOf hNX
  have hCX : C ≤ X := inf_le_left
  set W : Subgroup G := N ⊔ C with hW
  have hFr : X ≤ N ⊔ (X ⊓ normalizer (P : Set G)) := t59_frattini hNX hNn hP
  have hgW : ∀ g ∈ X ⊓ normalizer (P : Set G), ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    obtain ⟨hgX, hgP⟩ := hg
    obtain ⟨n, hn, c, hc, rfl⟩ := (mem_sup_of_le_normalizer (hCX.trans hXN)).1 hw
    have hgn : g * n * g⁻¹ ∈ N := (mem_normalizer_iff.mp (hXN hgX) n).mp hn
    have hgc : g * c * g⁻¹ ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨X.mul_mem (X.mul_mem hgX (hCX hc)) (X.inv_mem hgX), ?_⟩
      rw [mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g ∈ P := by
        refine (mem_normalizer_iff.mp hgP (g⁻¹ * y * g)).mpr ?_
        simpa [mul_assoc] using hy
      have hcomm : (g⁻¹ * y * g) * c = c * (g⁻¹ * y * g) := mem_centralizer_iff.mp hc.2 _ hy'
      calc y * (g * c * g⁻¹) = g * (((g⁻¹ * y * g)) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * y := by group
    have : g * (n * c) * g⁻¹ = (g * n * g⁻¹) * (g * c * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hgn hgc
  have hXW : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W := by
    intro x hx w hw
    obtain ⟨n', hn', g, hg, rfl⟩ :=
      (mem_sup_of_le_normalizer (inf_le_left.trans hXN)).1 (hFr hx)
    have h1 := hgW g hg w hw
    have hn'W : n' ∈ W := Subgroup.mem_sup_left hn'
    have : n' * g * w * (n' * g)⁻¹ = n' * (g * w * g⁻¹) * n'⁻¹ := by group
    rw [this]
    exact W.mul_mem (W.mul_mem hn'W h1) (W.inv_mem hn'W)
  have hN'n : (N.subgroupOf X).Normal := hNn
  set q : ↥X →* ↥X ⧸ N.subgroupOf X := QuotientGroup.mk' (N.subgroupOf X) with hq
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hq1 : ∀ x : ↥X, q x = 1 ↔ (x : G) ∈ N := fun x => QuotientGroup.eq_one_iff x
  set W' : Subgroup ↥X := W.subgroupOf X with hW'
  have hW'n : W'.Normal := ⟨fun w hw y => hXW y.1 y.2 w hw⟩
  set Wb : Subgroup (↥X ⧸ N.subgroupOf X) := W'.map q with hWb
  have hWbn : Wb.Normal := hW'n.map q hqs
  have hWb1 : Wb ≠ ⊥ := by
    intro hbot
    apply hC
    intro c hc
    have hcW' : (⟨c, hCX hc⟩ : ↥X) ∈ W' := Subgroup.mem_sup_right hc
    have h1 : q ⟨c, hCX hc⟩ ∈ Wb := ⟨_, hcW', rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact (hq1 ⟨c, hCX hc⟩).mp h1
  obtain ⟨K, ⟨hKn, hK1, hKW⟩, hKmin⟩ :=
    (Set.toFinite {K : Subgroup (↥X ⧸ N.subgroupOf X) | K.Normal ∧ K ≠ ⊥ ∧ K ≤ Wb}).exists_minimal
      ⟨Wb, hWbn, hWb1, le_rfl⟩
  have hKmin' : ∀ M : Subgroup (↥X ⧸ N.subgroupOf X), M ≤ K → M.Normal → M = ⊥ ∨ M = K := by
    intro M hMK hMn
    by_cases hM1 : M = ⊥
    · exact Or.inl hM1
    · exact Or.inr (le_antisymm hMK (hKmin ⟨hMn, hM1, hMK.trans hKW⟩ hMK))
  have hKres := h52iii (↥X ⧸ N.subgroupOf X) K hKn hK1 hKmin'
  have hKnorm : ∀ g : ↥X ⧸ N.subgroupOf X, g ∈ normalizer (K : Set (↥X ⧸ N.subgroupOf X)) := fun g => by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hKn.conj_mem h hh g, fun hh => ?_⟩
    have := hKn.conj_mem _ hh g⁻¹
    simpa [mul_assoc] using this
  have hRn : (oResOf p K).Normal := ⟨fun x hx g => conj_mem_oResOf (hKnorm g) hx⟩
  rcases hKmin' (oResOf p K) (oResOf_le p K) hRn with hR0 | hRK
  ·
    have hKp : IsPGroup p ↥K := fun k => by
      obtain ⟨e, he⟩ := exists_pow_mem_oResOf hp k.2
      refine ⟨e, Subtype.ext ?_⟩
      rw [hR0] at he
      simpa using he
    have hKle : K ≤ pCore p (↥X ⧸ N.subgroupOf X) := le_sSup ⟨hKn, hKp⟩
    rw [pCore_quotient_opStarP p X] at hKle
    exact hK1 (le_bot_iff.mp hKle)
  · have hresid : oResidual p ↥K = ⊤ := (oResidual_eq_top_iff K).mpr hRK
    have hKps : IsPStar p ↥K := by
      have h1 : IsPStar p ↥(⊤ : Subgroup ↥K) := hresid ▸ hKres
      exact IsPStar.of_mulEquiv (Subgroup.topEquiv (G := ↥K)) h1
    set M : Subgroup G := (K.comap q).map X.subtype with hM
    have hMX : M ≤ X := Subgroup.map_subtype_le _
    have hMsub : M.subgroupOf X = K.comap q :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    have hMn : (M.subgroupOf X).Normal := by rw [hMsub]; exact hKn.comap q
    have hmemM : ∀ x : ↥X, (x : G) ∈ M ↔ q x ∈ K := fun x => by
      have : x ∈ M.subgroupOf X ↔ x ∈ K.comap q := by rw [hMsub]
      exact this
    have hNM : N ≤ M := fun n hn => (hmemM ⟨n, hNX hn⟩).2 (by
      have : q ⟨n, hNX hn⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hn
      rw [this]; exact K.one_mem)
    have hMW : M ≤ N ⊔ C := by
      intro m hm
      have h1 : q ⟨m, hMX hm⟩ ∈ Wb := hKW ((hmemM ⟨m, hMX hm⟩).1 hm)
      obtain ⟨w, hw, hwm⟩ := h1
      have h2 : w⁻¹ * ⟨m, hMX hm⟩ ∈ N.subgroupOf X := QuotientGroup.eq.mp hwm
      have h3 : (w : G)⁻¹ * m ∈ N := h2
      have hwW : (w : G) ∈ W := hw
      have : m = (w : G) * ((w : G)⁻¹ * m) := by group
      rw [this]
      exact W.mul_mem hwW (Subgroup.mem_sup_left h3)
    have hNnM : (N.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr (hMX.trans hXN)
    let ψ : ↥M →* (↥X ⧸ N.subgroupOf X) := q.comp (Subgroup.inclusion hMX)
    have hψK : ∀ m : ↥M, ψ m ∈ K := fun m => (hmemM (Subgroup.inclusion hMX m)).1 m.2
    let ψ' : ↥M →* ↥K := ψ.codRestrict K hψK
    have hψ's : Function.Surjective ψ' := by
      intro k
      obtain ⟨x, hx⟩ := hqs k.1
      have hxM : (x : G) ∈ M := (hmemM x).2 (by rw [hx]; exact k.2)
      exact ⟨⟨x, hxM⟩, Subtype.ext hx⟩
    have hψ'ker : ψ'.ker = N.subgroupOf M := by
      ext m
      constructor
      · intro h
        have h1 : q (Subgroup.inclusion hMX m) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp h)
        exact (hq1 (Subgroup.inclusion hMX m)).1 h1
      · intro h
        exact MonoidHom.mem_ker.mpr (Subtype.ext ((QuotientGroup.eq_one_iff _).2 h))
    let e : ↥K ≃* ↥M ⧸ N.subgroupOf M :=
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hψ'ker)
    have hquot : IsPStar p (↥M ⧸ N.subgroupOf M) := IsPStar.of_mulEquiv e hKps
    have hcore : oResOf p M ≤ OpStar p X := t59_core h53 h56 hP hMX hNM hMn hMW hquot
    have hKbot : oResOf p K ≤ ⊥ := by
      refine oResOf_le_of fun k hk hkcop => ?_
      obtain ⟨a₀, ha₀⟩ := hψ's ⟨k, hk⟩
      have ha₀' : ψ a₀ = k := congrArg Subtype.val ha₀
      obtain ⟨a, ha, hacop⟩ := exists_coprime_lift hp ψ hkcop ha₀'
      have haM : (a : G) ∈ oResOf p M := mem_oResOf a.2 (by rwa [Subgroup.orderOf_coe])
      have haN : (a : G) ∈ N := opStar_le_opStarP p X (hcore haM)
      have h1 : ψ a = 1 := (QuotientGroup.eq_one_iff _).2 haN
      rw [← ha, h1]
      exact Subgroup.one_mem _
    exact hK1 (le_bot_iff.mp (hRK ▸ hKbot))

end CFSG.GH74.GLS.Balance
