module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3328
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem stmt3_3_29_of_F4
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) (h14 : Stmt3_3_14_F4)
    (h23 : Stmt3_3_23_F4) (h25 : Stmt3_3_25_F4) (h28 : Stmt3_3_28L32_F4) : Stmt3_3_29_F4 := by
  intro G _ _ T M L D h hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hML⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hML
  have hshort : IsShort2 L := by
    rcases (h25 G T M L D h).1 with hb | hb | hb
    · exact hb.1
    · exact hb.1
    · exact hb.1
  obtain ⟨-, hDT₀⟩ : IsLnBlock L 3 ∧
      D ≤ Subgroup.normalizer (preCenterAut T (vPlus L T) : Set G) := by
    rcases h23 G T M L D h hP with h1 | ⟨⟨h2c, -⟩, -⟩
    · exact h1
    · exact absurd h2c (not_hasNoncentralTwoChief_two_of_isShort2 hshort)
  obtain ⟨-, -, hFQ⟩ := h28 G T M L D h hP
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hQ2 : IsPGroup 2 ↥(qL L T) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQe : IsElemAbelian 2 (qL L T) := isElemAbelian_of_frattini_eq_bot hQ2 hFQ
  obtain ⟨hQT₀, -, hidx⟩ := h.preCenterAut_of_isPSL h38 h39 hTL hP
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hVQ : vPlus L T ≤ qL L T := hred.1.trans inf_le_left
  have hT₀T : preCenterAut T (vPlus L T) ≤ T := inf_le_left
  have hQN : L ⊔ T ≤ Subgroup.normalizer (qL L T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hT₀N : preCenterAut T (vPlus L T) ≤ Subgroup.normalizer (qL L T : Set G) :=
    hT₀T.trans (le_sup_right.trans hQN)
  have hQab : ∀ a ∈ qL L T, ∀ b ∈ qL L T, a * b = b * a := fun a ha b hb => by
    have := hQe.1
    exact setLike_mul_comm ha hb
  have hT₀C : preCenterAut T (vPlus L T) ⊓ Subgroup.centralizer (qL L T : Set G) = qL L T := by
    refine le_antisymm (fun x hx => ?_) (le_inf hQT₀ fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun z hz => hQab z hz y hy)
    rw [← hCQ]
    exact ⟨hT₀T (Subgroup.mem_inf.mp hx).1,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVQ) (Subgroup.mem_inf.mp hx).2⟩
  have hQne : qL L T ≠ ⊥ := h.toSetup331.pCoreOf_ne_bot
  have hDQ : ¬ D ≤ Subgroup.normalizer (qL L T : Set G) :=
    h.not_le_normalizer h38 h39 hQne (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hQN
  have hperm : ∀ g ∈ D, ∀ B, IsMaxElemAbelian (preCenterAut T (vPlus L T)) B →
      IsMaxElemAbelian (preCenterAut T (vPlus L T)) (B.map (MulAut.conj g).toMonoidHom) := by
    intro g hg B hB
    have hT₀g : (preCenterAut T (vPlus L T)).map (MulAut.conj g).toMonoidHom =
        preCenterAut T (vPlus L T) := A38.map_conj_eq_iff.mpr (hDT₀ hg)
    have := (isMaxElemAbelian_map_mulEquiv (MulAut.conj g)).mpr hB
    rwa [hT₀g] at this
  have hinQ : ∀ B, IsMaxElemAbelian (preCenterAut T (vPlus L T)) B → B ≤ qL L T →
      B = qL L T := fun B hB hBQ =>
    Subgroup.eq_of_le_of_card_ge hBQ (hB.2.2 _ hQT₀ hQe)
  apply hDQ
  by_cases hall : ∀ B, IsMaxElemAbelian (preCenterAut T (vPlus L T)) B → B ≤ qL L T
  ·
    obtain ⟨A₀, hA₀⟩ := GammaExtra.exists_isMaxElemAbelian (preCenterAut T (vPlus L T))
    have hQmax := (hinQ A₀ hA₀ (hall A₀ hA₀)) ▸ hA₀
    intro g hg
    exact A38.map_conj_eq_iff.mp (hinQ _ (hperm g hg _ hQmax) (hall _ (hperm g hg _ hQmax)))
  ·
    push Not at hall
    obtain ⟨A, hA, hAQ⟩ := hall
    obtain ⟨a, haA, haQ⟩ := IsConcreteLE.not_le_iff_exists.mp hAQ
    have hCA : qL L T ⊓ Subgroup.centralizer (A : Set G) =
        qL L T ⊓ Subgroup.centralizer ({a} : Set G) := by
      refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr haA))) fun y hy => ?_
      obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨hyQ, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      have hya : a * y = y * a := Subgroup.mem_centralizer_iff.mp hyC a rfl
      have hy := Subgroup.mem_inf.mpr ⟨hyQ, hyC⟩
      by_cases hbQ : b ∈ qL L T
      · exact hQab b hbQ y hyQ
      · have hab := hidx a (hA.1 haA) b (hA.1 hb) haQ hbQ
        have hy' := hQab _ hab y hyQ
        calc b * y = a * (a⁻¹ * b) * y := by group
          _ = a * (y * (a⁻¹ * b)) := by rw [mul_assoc, hy']
          _ = (a * y) * (a⁻¹ * b) := by group
          _ = (y * a) * (a⁻¹ * b) := by rw [hya]
          _ = y * b := by group
    have hAeq : ∀ B, IsMaxElemAbelian (preCenterAut T (vPlus L T)) B → ¬ B ≤ qL L T → B = A :=
      fun B hB hBQ => B2_21 hQe hQT₀ hT₀N hT₀C hA haA hCA hB
        ((h.autOn_eq_of_not_le h38 h39 hTL hP hQe hA.1 hAQ).trans
          (h.autOn_eq_of_not_le h38 h39 hTL hP hQe hB.1 hBQ).symm)
    have hAQcard : Nat.card ↥A ≤ Nat.card ↥(qL L T) := by
      have hidxA : ((A ⊓ qL L T).subgroupOf A).index = 2 := by
        rw [Subgroup.index_eq_two_iff]
        refine ⟨⟨a, haA⟩, fun b => ?_⟩
        simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
        have hbA : (b : G) ∈ A := b.2
        by_cases hb : (b : G) ∈ qL L T
        · have hba : (b : G) * a ∉ qL L T := fun h' => haQ (by
            have := (qL L T).mul_mem ((qL L T).inv_mem hb) h'
            simpa using this)
          simp only [hbA, hb, hba, A.mul_mem hbA haA, and_false, and_true]
          decide
        · have hba : (b : G) * a ∈ qL L T := by
            have hbinv : (b : G)⁻¹ ∈ preCenterAut T (vPlus L T) := inv_mem (hA.1 hbA)
            have := hidx _ hbinv a (hA.1 haA) (fun h' => hb (by simpa using inv_mem h')) haQ
            simpa using this
          simp only [hbA, hb, hba, A.mul_mem hbA haA, and_false, and_true]
          decide
      have hmul := Subgroup.card_mul_index ((A ⊓ qL L T).subgroupOf A)
      rw [hidxA, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hmul
      have hlt : A ⊓ qL L T ≠ qL L T := by
        intro heq
        apply haQ
        have hQA : qL L T ≤ A := heq ▸ inf_le_left
        rw [← hT₀C]
        refine ⟨hA.1 haA, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
        have := hA.2.1.1
        exact setLike_mul_comm (hQA hq) haA
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ qL L T ≤ qL L T)
      have hk1 : k ≠ 1 := by
        rintro rfl
        rw [mul_one] at hk
        exact hlt (Subgroup.eq_of_le_of_card_ge inf_le_right hk.le)
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hk
        exact Nat.card_pos.ne' hk
      rw [← hmul, hk]
      exact Nat.mul_le_mul_left _ (by omega)
    have hQmax : IsMaxElemAbelian (preCenterAut T (vPlus L T)) (qL L T) :=
      ⟨hQT₀, hQe, fun B hBT hBe => (hA.2.2 B hBT hBe).trans hAQcard⟩
    intro g hg
    have hodd : Odd (orderOf g) := by
      have h1 : orderOf (⟨g, hg⟩ : ↥D) ∣ Nat.card ↥D := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat h.Dodd h1
    have hQg := hperm g hg _ hQmax
    by_cases hgQ : (qL L T).map (MulAut.conj g).toMonoidHom ≤ qL L T
    · exact A38.map_conj_eq_iff.mp (hinQ _ hQg hgQ)
    ·
      have h1 := hAeq _ hQg hgQ
      have hAg := hperm g hg _ hA
      have h2 : A.map (MulAut.conj g).toMonoidHom = qL L T := by
        by_contra hne
        have hgA : ¬ A.map (MulAut.conj g).toMonoidHom ≤ qL L T := fun hle => hne (hinQ _ hAg hle)
        have h3 := hAeq _ hAg hgA
        apply hAQ
        have : qL L T = A := Subgroup.map_injective (MulAut.conj g).injective (h1.trans h3.symm)
        rw [← this]
      have hg2 : g ^ 2 ∈ Subgroup.normalizer (qL L T : Set G) := by
        refine A38.map_conj_eq_iff.mp ?_
        have e : (MulAut.conj (g ^ 2)).toMonoidHom =
            (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
          ext x
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
            Function.comp_apply]
          rw [pow_two]
          group
        rw [e, ← Subgroup.map_map, h1, h2]
      exact (Subgroup.zpowers_le.mpr hg2) (mem_zpowers_sq_of_odd hodd)

end CFSG.Quasithin.H13
