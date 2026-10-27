module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FinalAux

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section PGroup

variable {G : Type*} [Group G] [Finite G]

theorem i112v_inf_centralizer_ne_bot {p : ℕ} [Fact p.Prime] {Z B : Subgroup G}
    (hZ : IsPGroup p Z) (hB : IsPGroup p B) (hBZ : B ≤ Subgroup.normalizer (Z : Set G))
    (hne : Z ≠ ⊥) : Z ⊓ Subgroup.centralizer (B : Set G) ≠ ⊥ := by
  set P : Subgroup G := Z ⊔ B with hP
  have hPp : IsPGroup p P := IsPGroup.to_sup_of_normal_left' hZ hB hBZ
  have : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hZP : Z ≤ P := le_sup_left
  have hBP : B ≤ P := le_sup_right
  have hN : (Z.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hZP]
    intro z g hz hg
    have hle : P ≤ Subgroup.normalizer (Z : Set G) := sup_le Subgroup.le_normalizer hBZ
    exact (Subgroup.mem_normalizer_iff.1 (hle hg) z).1 hz
  have hne' : Z.subgroupOf P ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro z hz
    have : (⟨z, hZP hz⟩ : ↥P) ∈ Z.subgroupOf P := Subgroup.mem_subgroupOf.2 hz
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h
  obtain ⟨hwZ, hwc⟩ := Subgroup.mem_inf.1 hw
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨(w : G), Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 hwZ, ?_⟩⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := Subgroup.mem_center_iff.1 hwc ⟨b, hBP hb⟩
    exact congrArg Subtype.val this
  · intro h1
    apply hw1
    have h2 : (w : G) = 1 := congrArg Subtype.val h1
    exact Subtype.ext (Subtype.ext h2)

end PGroup

section Centre

variable {X : Type} [Group X] [Finite X] {B L : Subgroup X}

theorem i112v_Z_eq_bot (hL : IsComponentOf L ⊤)
    (hZ1 : Nat.card ↥(Subgroup.center ↥L) = 1) :
    i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) = ⊥ := by
  rw [i112_centre_J_eq hL, eq_bot_iff]
  refine iSup_le fun M => ?_
  have h : Nat.card ↥(centreIn (M : Subgroup X)) = 1 := by
    rw [i112_card_centreIn_orbit M.2, hZ1]
  exact le_bot_iff.2 (Subgroup.eq_bot_of_card_eq _ h)

theorem i112v_card_Z_inf_cent_le (hO : GLAPPrimeCore 3 X = ⊥) (hB : IsElemAbelian 3 B)
    (hL : GLAPComponent 3 ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = 3)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = 3) :
    Nat.card ↥((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓
      Subgroup.centralizer (B : Set X)) ≤ 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  obtain ⟨b, hbB, hbn⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (L : Set X) := by
    by_contra h
    exact hnL fun b hb => by_contra fun hb' => h ⟨b, hb, hb'⟩
  have horb := i112_orbit_eq_pow hp hB hidx hbB hbn
  have hZE := i112_isElemAbelian_Z (B := B) hLc (Or.inr hZc)
  have hcomm : ∀ a ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X),
      ∀ b ∈ i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb.2 a ha.1
  have hcyc : IsCyclic ↥(centreIn L) :=
    isCyclic_of_prime_card (by rw [card_centreIn, hZc])
  have e2 : centreIn (GLBConj b L) = (centreIn L).map (MulAut.conj b⁻¹).toMonoidHom :=
    centreIn_gLBConj b L
  have e3 : centreIn (GLBConj b (GLBConj b L)) =
      (centreIn (GLBConj b L)).map (MulAut.conj b⁻¹).toMonoidHom :=
    centreIn_gLBConj b (GLBConj b L)
  have key : ∀ M ∈ i112Orbit B L, centreIn M ≤
      centreIn L ⊔ centreIn (GLBConj b L) ⊔ centreIn (GLBConj b (GLBConj b L)) := by
    intro M hM
    have hM' := (Set.ext_iff.1 horb M).1 hM
    obtain ⟨i, hi, rfl⟩ := hM'
    have hi' : i < 3 := by simpa using hi
    interval_cases i
    · simp only [pow_zero, gLBConj_one]
      exact le_sup_left.trans le_sup_left
    · simp only [pow_one]
      exact le_sup_right.trans le_sup_left
    · simp only [pow_two, ← gLBConj_gLBConj]
      exact le_sup_right
  have h := card_inf_centralizer_le_of_conj hp _ (centreIn L) (centreIn (GLBConj b L))
    (centreIn (GLBConj b (GLBConj b L))) hcomm hZE.2 b⁻¹
    (fun v hv => i112_conj_mem_Z (B.inv_mem hbB) hv)
    (i112_centreIn_le_Z hLc i112_self_mem_orbit) hcyc e2.le e3.le
    (by rw [i112_centre_J_eq hLc]; exact iSup_le fun M => key M M.2)
  refine le_trans (Subgroup.card_le_of_le ?_) h
  intro v hv
  obtain ⟨hvZ, hvB⟩ := Subgroup.mem_inf.1 hv
  refine Subgroup.mem_inf.2 ⟨hvZ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.1 hvB b⁻¹ (B.inv_mem hbB)).symm

theorem i112v_card_Z_inf_cent_eq (hO : GLAPPrimeCore 3 X = ⊥) (hB : IsElemAbelian 3 B)
    (hL : GLAPComponent 3 ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = 3)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = 3) :
    Nat.card ↥((i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊓
      Subgroup.centralizer (B : Set X)) = 3 := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  set Z := i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) with hZdef
  have hZE := i112_isElemAbelian_Z (B := B) hLc (Or.inr hZc)
  have hZp : IsPGroup 3 Z := isPGroup_of_isElemAbelian hp hZE
  have hBp : IsPGroup 3 B := isPGroup_of_isElemAbelian hp hB
  have hBZ : B ≤ Subgroup.normalizer (Z : Set X) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact fun hv => i112_conj_mem_Z hy hv
    · intro hv
      have h1 := i112_conj_mem_Z (B.inv_mem hy) hv
      have h2 : y⁻¹ * (y * v * y⁻¹) * y⁻¹⁻¹ = v := by group
      rw [h2] at h1
      exact h1
  have hZne : Z ≠ ⊥ := by
    intro h
    have hle := i112_centreIn_le_Z (B := B) hLc i112_self_mem_orbit
    rw [← hZdef, h, le_bot_iff] at hle
    have h1 : Nat.card ↥(centreIn L) = 1 := by rw [hle, Subgroup.card_bot]
    rw [card_centreIn, hZc] at h1
    omega
  have hne := i112v_inf_centralizer_ne_bot hZp hBp hBZ hZne
  have hle := i112v_card_Z_inf_cent_le hO hB hL hnL hidx hZc
  have hsub : IsPGroup 3 ↥(Z ⊓ Subgroup.centralizer (B : Set X)) :=
    hZp.to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hsub
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hne (Subgroup.eq_bot_of_card_eq _ hk)
  rw [hk] at hle ⊢
  have : 3 ^ k ≥ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hk1 : k = 1 := by
    by_contra hk1
    have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hk1, pow_one]

theorem i112v_rank_lt (hO : GLAPPrimeCore 3 X = ⊥) (hB : IsElemAbelian 3 B)
    (hL : GLAPComponent 3 ⊤ L) (hnL : ¬ B ≤ Subgroup.normalizer (L : Set X))
    (hidx : (Subgroup.normalizer (L : Set X)).relIndex B = 3)
    (hZc : Nat.card ↥(Subgroup.center ↥L) = 3)
    (hZ9 : Nat.card ↥(i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X)) = 9)
    (hm : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L))
    (haut : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥L)) ≤ 2) :
    CFSG.Open.pRank 3 B < CFSG.Open.pRank 3
      ((B ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊔ i112J B L) := by
  classical
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp1 : 1 < 3 := by norm_num
  have : Fintype ↥(i112Orbit B L) := Fintype.ofFinite _
  have hLc : IsComponentOf L ⊤ := i116pI_isComponentOf hO hL
  obtain ⟨r, a, -, hrel, -, hHr, hBrank⟩ := i112_pRank_formula hp hB hnL
  have hr1 : r = 1 := by
    have h : (3 : ℕ) ^ r = 3 ^ 1 := by rw [← hrel, hidx, pow_one]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) h
  subst hr1
  have ha : a ≤ 2 := by
    have := i112_pRank_H_le (B := B) (L := L) hp1
    rw [hHr] at this
    omega
  set Z := i112J B L ⊓ Subgroup.centralizer (i112J B L : Set X) with hZdef
  have hZE := i112_isElemAbelian_Z (B := B) hLc (Or.inr hZc)
  have hBc : IsElemAbelian 3 (i112Bc B L) := isElemAbelian_of_le hB i112Bc_le_B
  obtain ⟨b, hb⟩ := exists_card_eq_of_isElemAbelian hp hBc
  have hbrank : CFSG.Open.pRank 3 (i112Bc B L) = b := pRank_eq_of_card hp1 hBc hb
  have hBcJ : i112Bc B L ≤ Subgroup.centralizer (i112J B L : Set X) := inf_le_right
  have hcommBZ : ∀ u ∈ i112Bc B L, ∀ v ∈ Z, u * v = v * u := fun u hu v hv =>
    (Subgroup.mem_centralizer_iff.1 (hBcJ hu) v hv.1).symm
  have hWZ : i112Bc B L ⊓ Z ≤ Z ⊓ B := fun v hv =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hv).2, i112Bc_le_B (Subgroup.mem_inf.1 hv).1⟩
  have hc1 := i112_pRank_Z_inf_B_le_one hp rfl hO hB hL hnL hidx hZc
  obtain ⟨hE₀a, hE₀card⟩ := card_mul_le_card_sup_mul_pow hp hBc hZE hcommBZ hWZ hc1
  obtain ⟨e₀, he₀⟩ := exists_card_eq_of_isElemAbelian hp hE₀a
  have he₀b : b + 1 ≤ e₀ := by
    rw [hb, hZ9, he₀, show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_add, ← pow_add] at hE₀card
    have := (Nat.pow_le_pow_iff_right hp1).1 hE₀card
    omega
  have hE₀cent : i112Bc B L ⊔ Z ≤
      Subgroup.centralizer ((⨆ i, i112Fam B L i : Subgroup X) : Set X) := by
    rw [i112_iSup_fam]
    exact sup_le hBcJ inf_le_right
  have hex : ∀ k : ↥(i112Orbit B L), ∃ E : Subgroup X, E ≤ (k : Subgroup X) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := fun k => by
    obtain ⟨E, hE, ha, hc⟩ := CFSG.SectionRank.exists_pRank hp1 (k : Subgroup X)
    exact ⟨E, hE, ha, by rw [hc, pRank_orbit_eq_top hp1 k.2]⟩
  choose E hEL hEa hEc using hex
  have hcomm : CommFam (i112Fam B L) := i112_commFam hLc
  have hz : ∀ k, CFSG.Open.pRank 3 (centreIn (i112Fam B L k)) ≤ 1 := fun k => by
    show CFSG.Open.pRank 3 (centreIn (k : Subgroup X)) ≤ 1
    rw [pRank_centreIn_orbit hp1 k.2]
    have hE : IsElemAbelian 3 (Subgroup.center ↥L) :=
      isElemAbelian_of_forall (fun u _ v hv => Subgroup.mem_center_iff.1 hv u) fun z hz => by
        have h1 : orderOf (⟨z, hz⟩ : Subgroup.center ↥L) ∣ 3 := hZc ▸ orderOf_dvd_natCard _
        exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.1 h1)
    rw [pRank_eq_of_card hp1 hE (by rw [hZc, pow_one])]
  have hH : (i112Bc B L ⊔ Z) ⊔ ⨆ k, E k ≤
      (B ⊓ Subgroup.centralizer (i112J B L : Set X)) ⊔ i112J B L := by
    refine sup_le (sup_le le_sup_left (inf_le_left.trans le_sup_right)) (iSup_le fun k => ?_)
    exact ((hEL k).trans (i112_orbit_le_J k.2)).trans le_sup_right
  have hrk := hcomm.le_pRank_add_card_mul hp hz hE₀cent hE₀a E hEL hEa he₀ hEc hH
  have hcard : Fintype.card ↥(i112Orbit B L) = 3 := by
    rw [← Nat.card_eq_fintype_card, i112_natCard_orbit, hidx]
  rw [hcard] at hrk
  simp only [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul] at hrk
  rw [hBrank, hbrank]
  omega

end Centre

end CFSG.HardMathSupport.Solomon.Coordinator
