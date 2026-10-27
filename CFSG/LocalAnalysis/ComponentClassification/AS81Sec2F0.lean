module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Sym

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem sec2S_le_normalizer_left (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : sec2S A R E F ≤ normalizer (E : Set G) :=
  sup_le (hF.F_le_normalizer hL hodd)
    fun _ hc => Sec2.sec2P_le E (mem_centralizerMod.mp hc).1

theorem card_inf_left (hF : Frame G A A R g E F) (hodd : Odd (Nat.card (center ↥A))) :
    Nat.card (E ⊓ A : Subgroup G) = 16 := by
  have hR := hF.sylowR
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hR.le hR.isPGroup hodd
  have := card_eq_card_inf_mul hR.le hF.R_le_E hF.E_le hRA1
  rw [hF.cardE, hF.cardR] at this
  omega

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))
  {x : G} (hx : x ∈ sec2P F) (hxS : x ∉ sec2S A R E F)

include h11 hE16 hF hL hodd hx hxS

theorem exists_mul_eq_of_mem_inf {c : G} (hc : c ∈ sec2P E ⊓ sec2S A R E F) :
    ∃ e ∈ E, ∃ y ∈ rightConjugate E x ⊓ sec2P E, c = e * y := by
  obtain ⟨-, hS⟩ := rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS
  have hEP : E ≤ sec2P E :=
    Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl
  have hN : rightConjugate E x ≤ normalizer (E : Set G) :=
    (hS ▸ le_sup_right : rightConjugate E x ≤ sec2S A R E F).trans
      (sec2S_le_normalizer_left hF hL hodd)
  have hc' : c ∈ ((E ⊔ rightConjugate E x : Subgroup G) : Set G) := by
    rw [← hS]
    exact hc.2
  rw [coe_mul_of_right_le_normalizer_left E _ hN] at hc'
  obtain ⟨e, he, y, hy, rfl⟩ := hc'
  refine ⟨e, he, y, ⟨hy, ?_⟩, rfl⟩
  have := (sec2P E).mul_mem ((sec2P E).inv_mem (hEP he)) hc.1
  simpa using this

theorem le_sec2P_inf_sec2S : E ≤ sec2P E ⊓ sec2S A R E F := by
  obtain ⟨-, hS⟩ := rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS
  exact le_inf (Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl)
    (hS ▸ le_sup_left)

theorem rightConjugate_inf_le : rightConjugate E x ⊓ sec2P E ≤ sec2P E ⊓ sec2S A R E F := by
  obtain ⟨-, hS⟩ := rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS
  exact fun y hy => ⟨hy.2, hS ▸ mem_sup_right hy.1⟩

theorem sec2Z_le_rightConjugate_inf : sec2Z A E F ≤ rightConjugate E x ⊓ sec2P E := by
  obtain ⟨hinf, -⟩ := rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS
  have hEP : E ≤ sec2P E :=
    Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl
  rw [← hinf]
  exact fun z hz => ⟨hz.1, hEP hz.2⟩

theorem inf_rightConjugate_inf_eq : E ⊓ (rightConjugate E x ⊓ sec2P E) = sec2Z A E F := by
  obtain ⟨hinf, -⟩ := rightConjugate_inf_eq_and_sec2S_eq h11 hE16 hF hL hodd hx hxS
  refine le_antisymm (fun y hy => ?_) (le_inf ?_ (sec2Z_le_rightConjugate_inf h11 hE16 hF hL hodd
    hx hxS))
  · rw [← hinf]
    exact ⟨hy.2.1, hy.1⟩
  · rw [← hinf]
    exact inf_le_right

theorem card_rightConjugate_inf : Nat.card (rightConjugate E x ⊓ sec2P E : Subgroup G) = 16 := by
  have hEP : E ≤ sec2P E :=
    Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE) le_normalizer le_rfl
  have hN : rightConjugate E x ⊓ sec2P E ≤ normalizer (E : Set G) :=
    fun y hy => Sec2.sec2P_le E hy.2
  have hsup : E ⊔ (rightConjugate E x ⊓ sec2P E) = sec2P E ⊓ sec2S A R E F := by
    refine le_antisymm (sup_le (le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS)
      (rightConjugate_inf_le h11 hE16 hF hL hodd hx hxS)) fun c hc => ?_
    obtain ⟨e, he, y, hy, rfl⟩ := exists_mul_eq_of_mem_inf h11 hE16 hF hL hodd hx hxS hc
    exact mul_mem (mem_sup_left he) (mem_sup_right hy)
  have hC : Nat.card (sec2P E ⊓ sec2S A R E F : Subgroup G) = 4 * 64 := by
    obtain ⟨hEC, hidx, -⟩ := centralizerMod_facts h11 hE16 hF hL hodd
    have h1 := relIndex_mul_card E (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F))
    rw [inf_eq_left.mpr hEC, hidx, hF.cardE] at h1
    rw [inf_comm, sec2S_inf_sec2P h11 hE16 hF hL hodd]
    exact h1.symm
  have h := card_sup_mul_card_inf (H := E) (R := rightConjugate E x ⊓ sec2P E) hN
  rw [hsup, inf_rightConjugate_inf_eq h11 hE16 hF hL hodd hx hxS, hC, hF.card_sec2Z hodd,
    hF.cardE] at h
  omega

omit hx hxS in
theorem rightConjugate_inf_le_centralizer :
    rightConjugate E x ⊓ sec2P E ≤ centralizer ((E ⊓ A : Subgroup G) : Set G) :=
  fun _ hy => sec2P_le_centralizer_inf h11 hE16 hF hL hodd hy.2

theorem inf_inf_rightConjugate_inf_eq :
    E ⊓ A ⊓ (rightConjugate E x ⊓ sec2P E) = sec2Z A E F := by
  have hZ := inf_rightConjugate_inf_eq h11 hE16 hF hL hodd hx hxS
  refine le_antisymm (fun y hy => hZ ▸ ⟨hy.1.1, hy.2⟩) (le_inf ?_
    (sec2Z_le_rightConjugate_inf h11 hE16 hF hL hodd hx hxS))
  rw [hF.sec2Z_eq]
  exact fun z hz => ⟨hz.1.1, hz.2⟩

omit hx hxS in
theorem isElemAbelian_sec2F0 : IsElemAbelian 2 (sec2F0 A E x) := by
  have hE' := AS76b.isElemAbelian_rightConjugate hF.elemE x
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE'c : ∀ a ∈ rightConjugate E x, ∀ b ∈ rightConjugate E x, a * b = b * a :=
    fun a ha b hb => congrArg Subtype.val (hE'.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hYW := rightConjugate_inf_le_centralizer (x := x) h11 hE16 hF hL hodd
  have key : ∀ a ∈ sec2F0 A E x, ∀ b ∈ sec2F0 A E x,
      a * a ∈ (⊥ : Subgroup G) ∧ a * b * a⁻¹ * b⁻¹ ∈ (⊥ : Subgroup G) := fun a ha b hb =>
    Sec2.sq_mem_and_commutator_mem_of_sup
      (fun _ _ => mem_centralizer_iff.mpr fun z hz => by
        rw [SetLike.mem_coe, mem_bot] at hz
        rw [hz, one_mul, mul_one])
      (fun y hy => centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun w hw =>
        (mem_centralizer_iff.mp (hYW hw) y hy).symm))
      (fun y hy y' hy' => hEc y hy.1 y' hy'.1)
      (fun y hy => by rw [← sq]; exact hF.elemE.2 y hy.1)
      (fun w hw w' hw' => hE'c w hw.1 w' hw'.1)
      (fun w hw => by rw [← sq]; exact hE'.2 w hw.1)
      (fun y hy w hw => by
        rw [mem_bot]
        have h := mem_centralizer_iff.mp (hYW hw) y hy
        calc y⁻¹ * w⁻¹ * y * w = y⁻¹ * w⁻¹ * (y * w) := by group
          _ = y⁻¹ * w⁻¹ * (w * y) := by rw [h]
          _ = 1 := by group) ha hb
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · have h := mem_bot.mp (key a a.2 b b.2).2
    show (a : G) * b = b * a
    calc (a : G) * b = (a * b * (a : G)⁻¹ * (b : G)⁻¹) * (b * a) := by group
      _ = b * a := by rw [h, one_mul]
  · rw [sq]
    exact mem_bot.mp (key a ha a ha).1

theorem card_sec2F0 : Nat.card (sec2F0 A E x) = 64 := by
  have hN : rightConjugate E x ⊓ sec2P E ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    fun y hy => centralizer_le_normalizer _
      (rightConjugate_inf_le_centralizer (x := x) h11 hE16 hF hL hodd hy)
  have h := card_sup_mul_card_inf (H := E ⊓ A) (R := rightConjugate E x ⊓ sec2P E) hN
  rw [inf_inf_rightConjugate_inf_eq h11 hE16 hF hL hodd hx hxS, hF.card_sec2Z hodd,
    card_inf_left hF hodd, card_rightConjugate_inf h11 hE16 hF hL hodd hx hxS] at h
  change Nat.card (sec2F0 A E x) * 4 = 16 * 16 at h
  omega

theorem sec2P_inf_sec2S_eq : sec2P E ⊓ sec2S A R E F = E ⊔ sec2F0 A E x := by
  refine le_antisymm (fun c hc => ?_) (sup_le (le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS)
    (sup_le ((inf_le_left).trans (le_sec2P_inf_sec2S h11 hE16 hF hL hodd hx hxS))
      (rightConjugate_inf_le h11 hE16 hF hL hodd hx hxS)))
  obtain ⟨e, he, y, hy, rfl⟩ := exists_mul_eq_of_mem_inf h11 hE16 hF hL hodd hx hxS hc
  exact mul_mem (mem_sup_left he) (mem_sup_right (mem_sup_right hy))

theorem mem_sec2F0_of_mul_self {u : G} (hu : u ∈ sec2P E ⊓ sec2S A R E F) (huE : u ∉ E)
    (hu2 : u * u = 1) : u ∈ sec2F0 A E x := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hE' := AS76b.isElemAbelian_rightConjugate hF.elemE x
  obtain ⟨e, he, y, hy, rfl⟩ := exists_mul_eq_of_mem_inf h11 hE16 hF hL hodd hx hxS hu
  have hyE : y ∉ E := fun h => huE (E.mul_mem he h)
  have hyN := Sec2.sec2P_le E hy.2
  have he1 : e⁻¹ = e := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hF.elemE.2 e he)
  have hy1 : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hE'.2 y hy.1)
  have hye : y * e * y⁻¹ = e := by
    calc y * e * y⁻¹ = e⁻¹ * (e * y * (e * y)) * y⁻¹ * y⁻¹ := by group
      _ = e⁻¹ * y⁻¹ * y⁻¹ := by rw [hu2, mul_one]
      _ = e := by rw [he1, hy1, mul_assoc, ← sq, ← hy1, inv_pow, hE'.2 y hy.1, inv_one, mul_one]
  have heA : e ∈ A := by
    by_contra heA
    obtain ⟨Q, hQ, heQ⟩ := hD.cover e he fun h => heA h.2
    have hQQ : rightConjugate Q y = Q := by
      by_contra hne
      have hmem : e ∈ rightConjugate Q y ⊓ Q :=
        ⟨(mem_rightConjugate_iff Q y e).mpr (by rw [hye]; exact heQ), heQ⟩
      rw [hD.disj _ (rightConjugate_mem_pointsIn hQ hyN) _ hQ hne, mem_bot] at hmem
      exact heA (hmem ▸ A.one_mem)
    have hfix : pointsAction R E ⟨y⁻¹, inv_mem hyN⟩ ⟨Q, hQ⟩ = ⟨Q, hQ⟩ := by
      apply Subtype.ext
      rw [coe_pointsAction_apply]
      show rightConjugate Q y⁻¹⁻¹ = Q
      rw [inv_inv, hQQ]
    have h := hD.mem_of_apply_eq hT hCE (p := ⟨y⁻¹, inv_mem hyN⟩) (inv_mem hy.2) hfix
    exact hyE (by simpa using E.inv_mem h)
  exact mul_mem (mem_sup_left ⟨he, heA⟩) (mem_sup_right hy)

theorem le_or_le_of_isElemAbelian {U : Subgroup G} (hU : U ≤ sec2P E ⊓ sec2S A R E F)
    (hUe : IsElemAbelian 2 U) : U ≤ E ∨ U ≤ sec2F0 A E x := by
  by_cases hUE : U ≤ E
  · exact Or.inl hUE
  right
  obtain ⟨u₀, hu₀U, hu₀E⟩ := IsConcreteLE.not_le_iff_exists.mp hUE
  have key : ∀ u ∈ U, u ∉ E → u ∈ sec2F0 A E x := fun u hu huE =>
    mem_sec2F0_of_mul_self h11 hE16 hF hL hodd hx hxS (hU hu) huE (by rw [← sq]; exact hUe.2 u hu)
  intro u hu
  by_cases huE : u ∈ E
  · have h1 : u * u₀ ∉ E := fun h => hu₀E (by simpa using E.mul_mem (E.inv_mem huE) h)
    have h2 := key _ (U.mul_mem hu hu₀U) h1
    simpa using (sec2F0 A E x).mul_mem h2 ((sec2F0 A E x).inv_mem (key u₀ hu₀U hu₀E))
  · exact key u hu huE

theorem not_rightConjugate_inf_le : ¬ rightConjugate E x ⊓ sec2P E ≤ E := fun h => by
  have h1 := inf_rightConjugate_inf_eq h11 hE16 hF hL hodd hx hxS
  rw [inf_eq_right.mpr h] at h1
  have h2 := card_rightConjugate_inf h11 hE16 hF hL hodd hx hxS
  rw [h1, hF.card_sec2Z hodd] at h2
  omega

theorem sec2P_le_normalizer_sec2F0 : sec2P E ≤ normalizer (sec2F0 A E x : Set G) := by
  have hPS := sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd
  have hF0 : sec2F0 A E x ≤ sec2P E ⊓ sec2S A R E F := by
    rw [sec2P_inf_sec2S_eq h11 hE16 hF hL hodd hx hxS]
    exact le_sup_right
  have hconj : ∀ p ∈ sec2P E, ∀ f ∈ sec2F0 A E x, p * f * p⁻¹ ∈ sec2F0 A E x := by
    intro p hp
    set U := rightConjugate (sec2F0 A E x) p⁻¹
    have hmem : ∀ f, f ∈ U ↔ p⁻¹ * f * p⁻¹⁻¹ ∈ sec2F0 A E x := fun f =>
      mem_rightConjugate_iff _ _ f
    have hUle : U ≤ sec2P E ⊓ sec2S A R E F := fun f hf => by
      rw [hmem] at hf
      have h := hF0 hf
      have hpN : p ∈ normalizer ((sec2P E : Subgroup G) : Set G) := le_normalizer hp
      refine ⟨?_, ?_⟩
      · have := (mem_normalizer_iff.mp hpN _).mp h.1
        simpa [mul_assoc] using this
      · have := (mem_normalizer_iff.mp (hPS hp) _).mp h.2
        simpa [mul_assoc] using this
    rcases le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS hUle
      (AS76b.isElemAbelian_rightConjugate (isElemAbelian_sec2F0 (x := x) h11 hE16 hF hL hodd) _)
      with hE | hF0'
    · exfalso
      apply not_rightConjugate_inf_le h11 hE16 hF hL hodd hx hxS
      intro y hy
      have hyF : y ∈ sec2F0 A E x := mem_sup_right hy
      have hyU : p * y * p⁻¹ ∈ U := (hmem _).mpr (by simpa [mul_assoc] using hyF)
      have h := (mem_normalizer_iff.mp (Sec2.sec2P_le E ((sec2P E).inv_mem hp)) _).mp (hE hyU)
      simpa [mul_assoc] using h
    · intro f hf
      exact hF0' ((hmem _).mpr (by simpa [mul_assoc] using hf))
  exact fun p hp => Sec2.mem_normalizer_of_forall_conj_mem (hconj p hp)

theorem sec2F0_inf_eq : sec2F0 A E x ⊓ E = E ⊓ A := by
  refine le_antisymm (fun f hf => ?_) (le_inf le_sup_left inf_le_left)
  have hN : rightConjugate E x ⊓ sec2P E ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) :=
    fun y hy => centralizer_le_normalizer _
      (rightConjugate_inf_le_centralizer (x := x) h11 hE16 hF hL hodd hy)
  have hf' : f ∈ ((sec2F0 A E x : Subgroup G) : Set G) := hf.1
  rw [sec2F0, coe_mul_of_right_le_normalizer_left _ _ hN] at hf'
  obtain ⟨a, ha, y, hy, rfl⟩ := hf'
  have hyE : y ∈ E := by simpa using E.mul_mem (E.inv_mem ha.1) hf.2
  have hyZ : y ∈ sec2Z A E F := by
    rw [← inf_rightConjugate_inf_eq h11 hE16 hF hL hodd hx hxS]
    exact ⟨hyE, hy⟩
  rw [hF.sec2Z_eq] at hyZ
  exact (E ⊓ A).mul_mem ha ⟨hyZ.1.1, hyZ.2⟩

theorem sec2F0_eq_sec2F0 {x' : G} (hx' : x' ∈ sec2P F) (hxS' : x' ∉ sec2S A R E F) :
    sec2F0 A E x' = sec2F0 A E x := by
  have hle : rightConjugate E x' ⊓ sec2P E ≤ sec2F0 A E x := by
    rcases le_or_le_of_isElemAbelian h11 hE16 hF hL hodd hx hxS
      (rightConjugate_inf_le h11 hE16 hF hL hodd hx' hxS')
      (AS76b.IsElemAbelian.mono (AS76b.isElemAbelian_rightConjugate hF.elemE x') inf_le_left)
      with h | h
    · exact absurd h (not_rightConjugate_inf_le h11 hE16 hF hL hodd hx' hxS')
    · exact h
  refine eq_of_le_of_card_ge (sup_le le_sup_left hle) ?_
  rw [card_sec2F0 h11 hE16 hF hL hodd hx hxS, card_sec2F0 h11 hE16 hF hL hodd hx' hxS']

end Frame

end CFSG.ComponentClassification.AS81
