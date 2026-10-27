module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Families

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

namespace Sec2

omit [Finite G] in
theorem rightConjugate_sec2P_le (E : Subgroup G) (n : G) :
    rightConjugate (sec2P E) n ≤ sec2P (rightConjugate E n) := by
  have hN := AschbacherTheorem3.rightConjugate_normalizer E n
  refine le_sec2P ((isPGroup_sec2P E).map _) ?_ ?_
  · rw [← hN]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate (sec2P_le E) n
  · rw [← hN, ← AschbacherTheorem3.rightConjugate_normalizer]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate (normalizer_le_normalizer_sec2P E) n

omit [Finite G] in
theorem sec2P_rightConjugate (E : Subgroup G) (n : G) :
    sec2P (rightConjugate E n) = rightConjugate (sec2P E) n := by
  refine le_antisymm ?_ (rightConjugate_sec2P_le E n)
  have h := rightConjugate_sec2P_le (rightConjugate E n) n⁻¹
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h
  have h2 := AschbacherTheorem3.rightConjugate_le_rightConjugate h n
  rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at h2

omit [Finite G] in
theorem commutator_mul_mul_of_commute {z₁ z₂ a b : G} (h1a : Commute z₁ a) (h1b : Commute z₁ b)
    (h2a : Commute z₂ a) (h2b : Commute z₂ b) (h12 : Commute z₁ z₂) :
    z₁ * a * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have c1 : Commute z₁ (a * z₂ * b * a⁻¹) :=
    ((h1a.mul_right h12).mul_right h1b).mul_right h1a.inv_right
  have c2 : Commute z₂ (b * a⁻¹ * b⁻¹) := (h2b.mul_right h2a.inv_right).mul_right h2b.inv_right
  calc z₁ * a * (z₂ * b) * (z₁ * a)⁻¹ * (z₂ * b)⁻¹
      = z₁ * (a * z₂ * b * a⁻¹) * z₁⁻¹ * b⁻¹ * z₂⁻¹ := by group
    _ = a * (z₂ * (b * a⁻¹ * b⁻¹) * z₂⁻¹) := by rw [c1.eq, mul_inv_cancel_right]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [c2.eq, mul_inv_cancel_right]; group

end Sec2

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

omit [Finite G] in
theorem sec2S_le_sec2H [Finite G] (hF : Frame G A A R g E F) : sec2S A R E F ≤ sec2H E F :=
  sup_le ((Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemF) le_normalizer le_rfl).trans
    le_sup_right) fun _ hc => mem_sup_left (mem_centralizerMod.mp hc).1

variable (h11 : Step11)
  {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
  (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A)))

include h11 hE16 hF hL hodd

theorem sec2H_le_normalizer_sec2S : sec2H E F ≤ normalizer (sec2S A R E F : Set G) :=
  sup_le (sec2P_le_normalizer_sec2S h11 hE16 hF hL hodd)
    (sec2P_F_le_normalizer_sec2S h11 hE16 hF hL hodd)

theorem normalizer_sec2S_le_normalizer_sec2H {x : G} (hx : x ∈ sec2P F)
    (hxS : x ∉ sec2S A R E F) {h : G} (hh : h ∈ sec2P E) (hhS : h ∉ sec2S A R E F)
    (h4 : 4 ^ 4 ≤ Nat.card (conjClosure (E ⊓ A) (sec2P F)))
    (h4' : 4 ^ 4 ≤ Nat.card (conjClosure (F ⊓ A) (sec2P E))) :
    normalizer (sec2S A R E F : Set G) ≤ normalizer (sec2H E F : Set G) := by
  intro n hn
  have hU := planes_sec2S_eq_conjSet_union h11 hE16 hF hL hodd hx hxS hh hhS h4 h4'
  obtain ⟨hES, hFS⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  have hP : ∀ V ∈ conjSet F (sec2H E F) ∪ conjSet E (sec2H E F), sec2P V ≤ sec2H E F := by
    rintro V (⟨θ, hθ, rfl⟩ | ⟨θ, hθ, rfl⟩)
    · rw [Sec2.sec2P_rightConjugate, ← (rightConjugate_eq_self_iff _ θ).mpr (le_normalizer hθ)]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_right θ
    · rw [Sec2.sec2P_rightConjugate, ← (rightConjugate_eq_self_iff _ θ).mpr (le_normalizer hθ)]
      exact AschbacherTheorem3.rightConjugate_le_rightConjugate le_sup_left θ
  have hplane : ∀ V : Subgroup G, V ∈ planes E F → V ≤ sec2S A R E F →
      rightConjugate V n ∈ conjSet F (sec2H E F) ∪ conjSet E (sec2H E F) := fun V hV hVS => by
    rw [← hU]
    refine ⟨rightConjugate_mem_planes hV n, ?_⟩
    rw [← (rightConjugate_eq_self_iff _ n).mpr hn]
    exact AschbacherTheorem3.rightConjugate_le_rightConjugate hVS n
  have hEn := hP _ (hplane E ⟨1, Or.inl (rightConjugate_one E).symm⟩ hES)
  have hFn := hP _ (hplane F ⟨1, Or.inr (rightConjugate_one F).symm⟩ hFS)
  rw [Sec2.sec2P_rightConjugate] at hEn hFn
  have hle : rightConjugate (sec2H E F) n ≤ sec2H E F := by
    rw [sec2H, rightConjugate_sup']
    exact sup_le hEn hFn
  have heq : rightConjugate (sec2H E F) n = sec2H E F :=
    eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  exact (rightConjugate_eq_self_iff _ n).mp heq

theorem isSylowOf_sec2Z_centralizer_sec2S :
    IsSylowOf 2 (sec2Z A E F) (centralizer (sec2S A R E F : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  obtain ⟨hES, -⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  have hZC : sec2Z A E F ≤ centralizer (sec2S A R E F : Set G) := by
    rw [← hZ]
    exact inf_le_right
  have hZ2 : IsPGroup 2 (sec2Z A E F) := (isPGroup_two_of_isElemAbelian hF.elemE).to_le
    (by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left)
  obtain ⟨Q, hQ, hZQ⟩ := AschbacherTheorem3.exists_isSylowOf_le hZ2 hZC
  have hQZ : Q ≤ sec2Z A E F := fun q hq => by
    obtain ⟨k, hk⟩ := hQ.isPGroup ⟨q, hq⟩
    have hqk : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hqE : q ∈ E := hCE q (Subgroup.centralizer_le hES (hQ.le hq)) k hqk
    rw [← hZ]
    exact ⟨hES hqE, hQ.le hq⟩
  rwa [le_antisymm hQZ hZQ] at hQ

theorem isSylowOf_sec2S_centralizerMod :
    IsSylowOf 2 (sec2S A R E F)
      (centralizerMod (normalizer (sec2S A R E F : Set G)) (sec2S A R E F) (sec2Z A E F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := isSylowOf_sec2S h11 hE16 hF hL hodd
  obtain ⟨hES, hFS⟩ := le_sec2S_and_le_sec2S (A := A) (R := R) hF
  have hZ := centerIn_sec2S_eq h11 hE16 hF hL hodd
  have hSZ : sec2S A R E F ≤ normalizer (sec2Z A E F : Set G) := fun s hs => by
    rw [← hZ]
    exact mem_normalizer_centerIn (le_normalizer hs)
  set M := centralizerMod (normalizer (sec2S A R E F : Set G)) (sec2S A R E F) (sec2Z A E F)
    with hM
  have hSM : sec2S A R E F ≤ M := fun s hs => mem_centralizerMod.mpr ⟨le_normalizer hs, hSZ hs,
    fun t ht => by
      have := (sq_mem_and_commutator_mem_sec2Z h11 hE16 hF hL hodd
        ((sec2S A R E F).inv_mem ht) ((sec2S A R E F).inv_mem hs)).2
      simpa using this⟩
  have hconj : ∀ q ∈ M, ∀ s ∈ sec2S A R E F, q * s * q⁻¹ * s⁻¹ ∈ sec2Z A E F := fun q hq s hs => by
    have h1 := (mem_centralizerMod.mp (M.inv_mem hq)).2.2 s hs
    have h2 : q * s * q⁻¹ * s⁻¹ = (s * (s⁻¹ * q⁻¹⁻¹ * s * q⁻¹) * s⁻¹) := by group
    rw [h2]
    exact (mem_normalizer_iff.mp (hSZ hs) _).mp h1
  have hnorm : ∀ q ∈ M, ∀ V : Subgroup G, sec2Z A E F ≤ V → V ≤ sec2S A R E F →
      q ∈ normalizer (V : Set G) := fun q hq V hZV hVS =>
    Sec2.mem_normalizer_of_forall_conj_mem fun v hv => by
      have h1 : q * v * q⁻¹ = (q * v * q⁻¹ * v⁻¹) * v := by group
      rw [h1]
      exact V.mul_mem (hZV (hconj q hq v (hVS hv))) hv
  have hMX : M ≤ centralizer (sec2Z A E F : Set G) ⊓
      centralizerMod ⊤ (R ⊔ sec2Z A E F) (sec2Z A E F) ⊓ normalizer (E : Set G) ⊓
        normalizer (F : Set G) := by
    intro q hq
    have hZE : sec2Z A E F ≤ E := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_left
    have hZF : sec2Z A E F ≤ F := by rw [hF.sec2Z_eq]; exact inf_le_left.trans inf_le_right
    have hRZS : R ⊔ sec2Z A E F ≤ sec2S A R E F := by
      rw [hF.sup_sec2Z]
      exact inf_le_left.trans hES
    refine ⟨⟨⟨?_, mem_centralizerMod.mpr ⟨mem_top q, (mem_centralizerMod.mp hq).2.1,
      fun w hw => (mem_centralizerMod.mp hq).2.2 w (hRZS hw)⟩⟩,
      hnorm q hq E hZE hES⟩, hnorm q hq F hZF hFS⟩
    have hq' : (⁅sec2S A R E F, sec2S A R E F⁆ : Subgroup G) ≤ centralizer ({q} : Set G) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def, mem_centralizer_singleton_iff]
      have ha' : q * a * q⁻¹ = (q * a * q⁻¹ * a⁻¹) * a := by group
      have hb' : q * b * q⁻¹ = (q * b * q⁻¹ * b⁻¹) * b := by group
      have hza := hconj q hq a ha
      have hzb := hconj q hq b hb
      have hcza : ∀ z ∈ sec2Z A E F, ∀ s ∈ sec2S A R E F, Commute z s := fun z hz s hs => by
        rw [← hZ] at hz
        exact (mem_centralizer_iff.mp hz.2 s hs).symm
      have key : q * (a * b * a⁻¹ * b⁻¹) * q⁻¹ = a * b * a⁻¹ * b⁻¹ := by
        have hzbS : q * b * q⁻¹ * b⁻¹ ∈ sec2S A R E F := hES (hZE hzb)
        calc q * (a * b * a⁻¹ * b⁻¹) * q⁻¹ = (q * a * q⁻¹) * (q * b * q⁻¹) * (q * a * q⁻¹)⁻¹ *
              (q * b * q⁻¹)⁻¹ := by group
          _ = (q * a * q⁻¹ * a⁻¹) * a * ((q * b * q⁻¹ * b⁻¹) * b) *
              ((q * a * q⁻¹ * a⁻¹) * a)⁻¹ * ((q * b * q⁻¹ * b⁻¹) * b)⁻¹ := by rw [← ha', ← hb']
          _ = a * b * a⁻¹ * b⁻¹ := Sec2.commutator_mul_mul_of_commute (hcza _ hza a ha)
              (hcza _ hza b hb) (hcza _ hzb a ha) (hcza _ hzb b hb) (hcza _ hza _ hzbS)
      calc a * b * a⁻¹ * b⁻¹ * q = q * (a * b * a⁻¹ * b⁻¹) * q⁻¹ * q := by rw [key]
        _ = q * (a * b * a⁻¹ * b⁻¹) := by group
    rw [commutator_sec2S_eq h11 hE16 hF hL hodd] at hq'
    exact mem_centralizer_iff.mpr fun z hz => mem_centralizer_singleton_iff.mp (hq' hz)
  obtain ⟨Q, hQ, hSQ⟩ := AschbacherTheorem3.exists_isSylowOf_le hsyl.isPGroup hSM
  have hQS := hsyl.eq_of_le hSQ (hQ.le.trans hMX) hQ.isPGroup
  rwa [hQS] at hQ

end Frame

end CFSG.ComponentClassification.AS81
