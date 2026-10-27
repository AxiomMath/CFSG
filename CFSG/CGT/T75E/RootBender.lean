module

public import CFSG.CGT.T75E.RootOrders
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.CGT.Timmesfeld75.BenderInputs5
public import CFSG.CGT.Timmesfeld75.MaxPairDichotomy
public import CFSG.CGT.Timmesfeld75.Sec4TwoBender
public import CFSG.CGT.Timmesfeld75.ListWCLinPSL

public noncomputable section

namespace CFSG.CGT.T75E

open CFSG.CGT.Timmesfeld75 CFSG.BenderSuzuki CFSG.Open CFSG.Assembly.LowTwoRank

section Quot

variable {K : Type} [Group K] [Finite K]

theorem sup_conj_isBender (hAsc : AschbacherNoPolarInput) (hK : IsBenderGroup K)
    {T : Subgroup K} (hT : IsWC T) (hT1 : T ≠ ⊥) (h4 : 4 ≤ Nat.card T) {g : K}
    (hg : conjSubgroup g T ≠ T) :
    IsBenderGroup (↥(T ⊔ conjSubgroup g T) ⧸ Subgroup.center ↥(T ⊔ conjSubgroup g T)) := by
  set X : Subgroup K := T ⊔ conjSubgroup g T with hXdef
  have hTX : T ≤ X := le_sup_left
  have hT'X : conjSubgroup g T ≤ X := le_sup_right
  have hSW : StrongWC T :=
    strongWC_of_normIn_eq_bot hT fun g hg => benderWCInput_of_repo K hK T hT hT1 g hg
  have hSWX : StrongWC (T.subgroupOf X) := hSW.subgroupOf X
  obtain ⟨x, hxX, hx⟩ := exists_mem_conj_eq_of_le hT hTX hT'X
  have hconjX : (conjSubgroup g T).subgroupOf X = conjSubgroup (⟨x, hxX⟩ : X) (T.subgroupOf X) := by
    rw [conjSubgroup_subgroupOf, hx]
  have hcl : Subgroup.normalClosure ((T.subgroupOf X : Subgroup ↥X) : Set ↥X) = ⊤ := by
    have hX1 : (T.subgroupOf X) ⊔ ((conjSubgroup g T).subgroupOf X) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hTX hT'X]
      exact Subgroup.subgroupOf_self X
    refine eq_top_iff.2 (hX1 ▸ sup_le Subgroup.le_normalClosure ?_)
    rw [hconjX]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have := (Subgroup.normalClosure_normal
      (s := ((T.subgroupOf X : Subgroup ↥X) : Set ↥X))).conj_mem
      a (Subgroup.le_normalClosure ha) ⟨x, hxX⟩
    simpa [MulAut.conj_apply] using this
  have hnn : ¬ ∀ y : ↥X, conjSubgroup y (T.subgroupOf X) = T.subgroupOf X := by
    intro h
    apply hg
    have h1 := h ⟨x, hxX⟩
    rw [← hconjX, Subgroup.subgroupOf_inj, inf_eq_left.2 hT'X, inf_eq_left.2 hTX] at h1
    exact h1
  have h4X : 4 ≤ Nat.card (T.subgroupOf X) := by
    have : Nat.card (T.subgroupOf X) = Nat.card T := by
      rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective X),
        Subgroup.map_subgroupOf_eq_of_le hTX]
    omega
  exact lemma25_top_of_not_normal hAsc hSWX hcl hnn h4X

end Quot

section U3

variable {K : Type} [Group K] [Finite K] {Tb : Subgroup K} {c₁ c₂ : K} {f : ℕ}

theorem conjSubgroup_eq_self_of_commute {G : Type*} [Group G] {a : G} {A : Subgroup G}
    (h : ∀ x ∈ A, Commute a x) : conjSubgroup a A = A := by
  have key : ∀ y ∈ A, a⁻¹ * y * a = y := by
    intro y hy
    have h1 := (h y hy).eq
    calc a⁻¹ * y * a = a⁻¹ * (y * a) := by group
      _ = a⁻¹ * (a * y) := by rw [h1]
      _ = y := by group
  ext y
  rw [mem_conjSubgroup]
  constructor
  · intro hy
    have h1 := (h _ hy).eq
    have : y = a⁻¹ * y * a := by
      calc y = a * (a⁻¹ * y * a) * a⁻¹ := by group
        _ = (a⁻¹ * y * a) * a * a⁻¹ := by rw [h1]
        _ = a⁻¹ * y * a := by group
    rwa [this]
  · intro hy
    rw [key y hy]
    exact hy

theorem card_le_two_pow_of_sq_eq_one (hf : 2 ≤ f) (A : Subgroup (PSU3Model f))
    (hA : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 2 ^ f := by
  have hQ : IsBenderGroup (PSU3Model f) := .isPSU3 f hf (MulEquiv.refl _)
  have hB : fusionBenderBorel (PSU3Model f) (2 ^ f) 3 := bender_psu3_borel_full f hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 A := fun x => ⟨1, by
    have := hA x x.2
    rw [pow_one, pow_two]
    exact Subtype.ext this⟩
  obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
  have hle : A ≤ (Subgroup.center (S : Subgroup (PSU3Model f))).map
      (S : Subgroup (PSU3Model f)).subtype := by
    intro a ha
    refine ⟨⟨a, hAS ha⟩, Subgroup.mem_center_iff.2 fun y => ?_, rfl⟩
    exact Subtype.ext (CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hQ S
      (hAS ha) (hA a ha) y y.2).symm
  calc Nat.card A ≤ Nat.card ((Subgroup.center (S : Subgroup (PSU3Model f))).map
        (S : Subgroup (PSU3Model f)).subtype) := Subgroup.card_le_of_le hle
    _ = Nat.card (Subgroup.center (S : Subgroup (PSU3Model f))) :=
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    _ = 2 ^ f := (hB S).2.2.2.1

theorem rootGroup_u3 (hAsc : AschbacherNoPolarInput) {m : ℕ}
    (hm : 2 ≤ m) (hG : CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSU 3 2 m)
    (hT : IsWC Tb) (hT1 : Tb ≠ ⊥) (hf : 2 ≤ f) (ρ : ↥(Y3 Tb c₁ c₂) →* PSU3Model f)
    (hρ : Function.Surjective ρ) : Y3 Tb c₁ c₂ = ⊤ := by
  obtain ⟨e⟩ := exists_psu3_of_statedClassicalModel hm hG
  have hK : IsBenderGroup K := .isPSU3 m hm (e.trans (MulEquiv.subgroupCongr
    (show CFSG.Open.PSU3 2 m = PSU3Model m from rfl)))
  obtain ⟨⟨hTcard, -, -⟩, -⟩ := psu3_wc hm hG hT hT1
  have h4 : 4 ≤ Nat.card Tb := by
    rw [hTcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hne : conjSubgroup c₁ Tb ≠ Tb := by
    intro h
    refine Y3_ne_sup ρ hρ hT hf 0 2 ?_
    simp only [Y3, T3, h, sup_idem]
    rfl
  set X : Subgroup K := Tb ⊔ conjSubgroup c₁ Tb with hX
  have hTX : Tb ≤ X := le_sup_left
  have hT1X : conjSubgroup c₁ Tb ≤ X := le_sup_right
  have hXY : X ≤ Y3 Tb c₁ c₂ := le_sup_of_le_left le_rfl
  have hXB := sup_conj_isBender hAsc hK hT hT1 h4 hne
  have hXS : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) :=
    CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isSimpleGroup hXB
  have hcenter : ∀ t : K, ∀ ht : t ∈ Tb, (⟨t, hTX ht⟩ : ↥X) ∈ Subgroup.center ↥X → t = 1 := by
    intro t ht hz
    by_contra ht1
    have hcent : conjSubgroup c₁ Tb ≤ Subgroup.centralizer ({t} : Set K) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_center_iff.1 hz ⟨w, hT1X hw⟩
      exact congrArg Subtype.val this
    exact hne ((hT.2 t ht ht1).2 c₁ hcent)
  let ρX : ↥X →* PSU3Model f := ρ.comp (Subgroup.inclusion hXY)
  have hρX : ∀ x : ↥X, ρX x = ρ ⟨x, hXY x.2⟩ := fun x => rfl
  have hNker : (ρX.ker.map (QuotientGroup.mk' (Subgroup.center ↥X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (ρX.ker.map (QuotientGroup.mk' (Subgroup.center ↥X))) with hbot | htop
  ·
    have hker : ∀ n : ↥X, ρX n = 1 → n ∈ Subgroup.center ↥X := by
      intro n hn
      have : QuotientGroup.mk' (Subgroup.center ↥X) n ∈
          ρX.ker.map (QuotientGroup.mk' (Subgroup.center ↥X)) :=
        Subgroup.mem_map_of_mem _ (MonoidHom.mem_ker.2 hn)
      rw [hbot, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff n).1 this
    have hinj : ∀ a ∈ (Tb.subgroupOf (Y3 Tb c₁ c₂) : Subgroup ↥(Y3 Tb c₁ c₂)),
        ∀ b ∈ (Tb.subgroupOf (Y3 Tb c₁ c₂) : Subgroup ↥(Y3 Tb c₁ c₂)), ρ a = ρ b → a = b := by
      intro a ha b hb hab
      have haT : (a : K) ∈ Tb := ha
      have hbT : (b : K) ∈ Tb := hb
      have hmem : ((a : K)⁻¹ * b) ∈ Tb := Tb.mul_mem (Tb.inv_mem haT) hbT
      have hrho : ρX ⟨(a : K)⁻¹ * b, hTX hmem⟩ = 1 := by
        have : (⟨(a : K)⁻¹ * b, hXY (hTX hmem)⟩ : ↥(Y3 Tb c₁ c₂)) = a⁻¹ * b := rfl
        rw [hρX, this, map_mul, map_inv, hab, inv_mul_cancel]
      have h1 : (a : K)⁻¹ * b = 1 := hcenter _ hmem (hker _ hrho)
      exact Subtype.ext (inv_mul_eq_one.1 h1)
    have hcardA : Nat.card (imgA ρ Tb) = Nat.card Tb := by
      unfold imgA
      rw [card_map_of_injOn ρ hinj, ← Subgroup.card_map_of_injective
        (Subgroup.subtype_injective (Y3 Tb c₁ c₂)),
        Subgroup.map_subgroupOf_eq_of_le (show Tb ≤ Y3 Tb c₁ c₂ from T3_le_Y3 Tb c₁ c₂ 0)]
    have hle : 2 ^ m ≤ 2 ^ f := by
      rw [← hTcard, ← hcardA]
      exact card_le_two_pow_of_sq_eq_one hf _ (imgA_sq ρ hT 0)
    have hmf : m ≤ f := (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
    obtain ⟨r, hr, hQcard⟩ := exists_odd_card_psu3Model (f := f) (by omega)
    obtain ⟨r', hr', hKcard'⟩ := exists_odd_card_psu3Model (f := m) (by omega)
    have hKcard : Nat.card K = 2 ^ (3 * m) * r' := by
      rw [Nat.card_congr e.toEquiv]
      exact hKcard'
    have hdvd : Nat.card (PSU3Model f) ∣ Nat.card K := card_psu3_dvd_card ρ hρ
    have h3f : 3 * f ≤ 3 * m := by
      refine le_of_two_pow_dvd_mul_odd hr' ?_
      rw [← hKcard]
      exact (Dvd.intro _ hQcard.symm).trans hdvd
    have hfm : f = m := by omega
    have hQK : Nat.card (PSU3Model f) = Nat.card K := by
      rw [Nat.card_congr e.toEquiv, hfm]
      rfl
    have hYK : Nat.card (Y3 Tb c₁ c₂) = Nat.card K := by
      refine Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _) ?_
      rw [← hQK]
      exact Subgroup.card_dvd_of_surjective hρ
    exact Subgroup.eq_top_of_card_eq _ hYK
  ·
    have hcomm : ∀ x y : ↥X, Commute (ρX x) (ρX y) := by
      have hz : ∀ x : ↥X, ∃ z ∈ Subgroup.center ↥X, ρX x = ρX z := by
        intro x
        have hx : QuotientGroup.mk' (Subgroup.center ↥X) x ∈
            ρX.ker.map (QuotientGroup.mk' (Subgroup.center ↥X)) := by
          rw [htop]
          trivial
        obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 hx
        refine ⟨n⁻¹ * x, QuotientGroup.eq.1 hnx, ?_⟩
        rw [map_mul, map_inv, MonoidHom.mem_ker.1 hn, inv_one, one_mul]
      intro x y
      obtain ⟨z, hz1, hzx⟩ := hz x
      obtain ⟨z', hz1', hzy⟩ := hz y
      rw [hzx, hzy, Commute, SemiconjBy, ← map_mul, ← map_mul,
        (Subgroup.mem_center_iff.1 hz1' z)]
    obtain ⟨y, hyX, hy⟩ := exists_mem_conj_eq_of_le hT hTX hT1X
    have hA1 : imgA ρ (T3 Tb c₁ c₂ 1) = imgA ρ Tb := by
      have h1 : imgA ρ (T3 Tb c₁ c₂ 1) =
          conjSubgroup (ρ ⟨y, hXY hyX⟩) (imgA ρ Tb) := by
        unfold imgA
        rw [T3_one, hy, ← conjSubgroup_subgroupOf (Y3 Tb c₁ c₂) Tb ⟨y, hXY hyX⟩,
          map_conjSubgroup]
      rw [h1]
      apply conjSubgroup_eq_self_of_commute
      rintro _ ⟨t, ht, rfl⟩
      have htK : (t : K) ∈ Tb := ht
      exact hcomm ⟨y, hyX⟩ ⟨t, hTX htK⟩
    have hsup := iSup_imgA ρ hρ
    have h0 : imgA ρ (T3 Tb c₁ c₂ 0) = imgA ρ Tb := rfl
    rw [hA1, h0, sup_idem] at hsup
    exact absurd hsup (imgA_sup_ne_top ρ hT hf 0 2)

end U3

end CFSG.CGT.T75E
