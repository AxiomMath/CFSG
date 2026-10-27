module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19Iface
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf13Abel
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf16F7

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

theorem q8_central_dec : ∀ q : QuaternionGroup 2, (∀ r : QuaternionGroup 2, q * r = r * q) →
    q = 1 ∨ q = QuaternionGroup.a 2 := by decide

theorem q8_invol_dec :
    ∀ q : QuaternionGroup 2, q * q = 1 → q ≠ 1 → q = QuaternionGroup.a 2 := by decide

section Q8

variable {G : Type} [Group G]

theorem central_eq_of_q8 {L : Subgroup G} {t : G} (hq : Nonempty (↥L ≃* QuaternionGroup 2))
    (ht : IsUniqueInvolution L t) {a : G} (ha : a ∈ L) (hc : ∀ k ∈ L, a * k = k * a) :
    a = 1 ∨ a = t := by
  obtain ⟨e⟩ := hq
  have h1 : ∀ r : QuaternionGroup 2, e ⟨a, ha⟩ * r = r * e ⟨a, ha⟩ := by
    intro r
    obtain ⟨k, rfl⟩ := e.surjective r
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc k.1 k.2)
  have h3 : e ⟨t, ht.mem⟩ = QuaternionGroup.a 2 := by
    apply q8_invol_dec
    · rw [← map_mul]
      have : (⟨t, ht.mem⟩ * ⟨t, ht.mem⟩ : ↥L) = 1 := Subtype.ext ht.sq
      rw [this, map_one]
    · intro h
      apply ht.ne_one
      have : (⟨t, ht.mem⟩ : ↥L) = 1 := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val this
  rcases q8_central_dec _ h1 with h2 | h2
  · left
    have : (⟨a, ha⟩ : ↥L) = 1 := e.injective (h2.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · right
    have : (⟨a, ha⟩ : ↥L) = ⟨t, ht.mem⟩ := e.injective (h2.trans h3.symm)
    exact congrArg Subtype.val this

end Q8

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem comm_pair : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a :=
  OddQuot.commutes_of_twin_pgroup S.hs.hyp S.hs.two S.hK S.hK'.1 (Ne.symm S.hne) S.hz S.hz'

theorem exists_mul_of_mem_sup {x : G} (hx : x ∈ K ⊔ K') : ∃ a ∈ K, ∃ b ∈ K', x = a * b := by
  let H : Subgroup G :=
    { carrier := {x | ∃ a ∈ K, ∃ b ∈ K', x = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', K.mul_mem ha ha', b * b', K'.mul_mem hb hb', ?_⟩
        have hba : b * a' = a' * b := (S.comm_pair a' ha' b hb).symm
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [hba]
          _ = a * a' * (b * b') := by group
      one_mem' := ⟨1, K.one_mem, 1, K'.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, K.inv_mem ha, b⁻¹, K'.inv_mem hb, ?_⟩
        have hab := S.comm_pair a ha b hb
        calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [hab]
          _ = a⁻¹ * b⁻¹ := by group }
  have hle : K ⊔ K' ≤ H :=
    sup_le (fun a ha => ⟨a, ha, 1, K'.one_mem, by simp⟩)
      (fun b hb => ⟨1, K.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem pairInv_commute {u : G} (hu : PairInv K K' z π g u) : ∀ x ∈ piGen π, x * u = u * x := by
  intro x hx
  have h : K ⊔ K' ≤ Subgroup.centralizer (piGen π : Set G) :=
    sup_le S.pair_le_cent.1 S.pair_le_cent.2
  exact (Subgroup.mem_centralizer_iff.mp (h hu.1)) x hx

theorem mem_centMembers_of_pi {u : G} (hX : ∀ x ∈ piGen π, x * u = u * x) {M : Subgroup G}
    (hM : M ∈ π) : M ∈ centMembers (CoreAssembly.conjClass K₀) u :=
  ⟨S.mem_of_mem_pi hM, fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hX x (le_piGen hM hx))⟩

theorem piGen_le_centLayer {u : G} (hX : ∀ x ∈ piGen π, x * u = u * x) :
    piGen π ≤ centLayer (CoreAssembly.conjClass K₀) u :=
  piGen_le fun _ hM => le_centLayer (S.mem_centMembers_of_pi hX hM)

theorem pair_not_cent {u : G} (hu : PairInv K K' z π g u) :
    (∃ k ∈ K, u * k ≠ k * u) ∧ (∃ k ∈ K', u * k ≠ k * u) := by
  obtain ⟨hu1, -, hu2, hu3, hu4⟩ := hu
  obtain ⟨a, ha, b, hb, rfl⟩ := S.exists_mul_of_mem_sup hu1
  have hKq := S.iso_q8 S.hK
  have hK'q := S.iso_q8 S.hK'.1
  have hzK' : z ∈ K' := S.hz'.mem
  have hzK : z ∈ K := S.hz.mem
  have hinvK' : a * b ∈ K' → False := by
    intro h
    rcases S.hz'.unique _ h hu2 with h1 | h1
    · exact hu3 h1
    · exact hu4 h1
  have hinvK : a * b ∈ K → False := by
    intro h
    rcases S.hz.unique _ h hu2 with h1 | h1
    · exact hu3 h1
    · exact hu4 h1
  constructor
  · by_contra hall
    push Not at hall
    have hac : ∀ k ∈ K, a * k = k * a := by
      intro k hk
      have h1 := hall k hk
      have hbk : b * k = k * b := (S.comm_pair k hk b hb).symm
      have hbk' : b⁻¹ * k = k * b⁻¹ := (Commute.inv_left (show Commute b k from hbk)).eq
      calc a * k = (a * b) * (b⁻¹ * k) := by group
        _ = (a * b) * (k * b⁻¹) := by rw [hbk']
        _ = ((a * b) * k) * b⁻¹ := by group
        _ = (k * (a * b)) * b⁻¹ := by rw [h1]
        _ = k * a := by group
    rcases central_eq_of_q8 hKq S.hz ha hac with h | h
    · apply hinvK'
      rw [h, one_mul]
      exact hb
    · apply hinvK'
      rw [h]
      exact K'.mul_mem hzK' hb
  · by_contra hall
    push Not at hall
    have hbc : ∀ k ∈ K', b * k = k * b := by
      intro k hk
      have h1 := hall k hk
      have hak : a * k = k * a := S.comm_pair a ha k hk
      have hak' : a⁻¹ * k = k * a⁻¹ := (Commute.inv_left (show Commute a k from hak)).eq
      calc b * k = a⁻¹ * ((a * b) * k) := by group
        _ = a⁻¹ * (k * (a * b)) := by rw [h1]
        _ = (a⁻¹ * k) * (a * b) := by group
        _ = (k * a⁻¹) * (a * b) := by rw [hak']
        _ = k * b := by group
    rcases central_eq_of_q8 hK'q S.hz' hb hbc with h | h
    · apply hinvK
      rw [h, mul_one]
      exact ha
    · apply hinvK
      rw [h]
      exact K.mul_mem ha hzK

theorem singleOrbit (hF7 : F7Cent K₀ π g)
    (hβ : betaOf (nbrAdj (CoreAssembly.conjClass K₀)) (CoreAssembly.conjClass K₀) π = {K, K'})
    {u : G} (hu : PairInv K K' z π g u) :
    ∀ L ∈ centMembers (CoreAssembly.conjClass K₀) u,
      ∃ x ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub x (conjSub g K) = L := by
  intro L hL
  by_contra hnot
  push Not at hnot
  have hX := S.pairInv_commute hu
  have hXY := S.piGen_le_centLayer hX
  have hLΩ : L ∈ CoreAssembly.conjClass K₀ := hL.1
  have hcomm : ∀ J ∈ π, Commutes L J := by
    intro J hJ x hx y hy
    have hJP := S.mem_centMembers_of_pi hX hJ
    have hnc : ¬ ∃ w ∈ centLayer (CoreAssembly.conjClass K₀) u, conjSub w J = L := by
      rintro ⟨w, hw, hwJ⟩
      obtain ⟨x', hx', hxJ⟩ := S.trans_pi _ S.hg J hJ
      refine hnot (w * x') ((centLayer (CoreAssembly.conjClass K₀) u).mul_mem hw (hXY hx')) ?_
      rw [conjSub_mul, hxJ, hwJ]
    exact (hF7 u hu.2.1 hX hu.2.2.2.1 J hJP L hL hnc y hy x hx).symm
  have hLX : Commutes L (piGen π) := commutes_piGen_of hcomm
  obtain ⟨t, ht⟩ := (S.hs.hyp.omega1 L hLΩ).1
  have hbeta := S.hos.mem_beta_of_centralizes S.hπ S.hH1 hLΩ ht
    (fun x hx => (hLX t ht.mem x hx).symm)
  rw [hβ] at hbeta
  obtain ⟨hK, hK'⟩ := S.pair_not_cent hu
  rcases hbeta with rfl | rfl
  · obtain ⟨k, hk, hne⟩ := hK
    exact hne (Subgroup.mem_centralizer_singleton_iff.mp (hL.2 hk)).symm
  · obtain ⟨k, hk, hne⟩ := hK'
    exact hne (Subgroup.mem_centralizer_singleton_iff.mp (hL.2 hk)).symm

theorem centLayer_ne_top (hS : IsSimpleGroup ↥(genFittingFStar G))
    (hnab : ∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) {u : G} (hu1 : u ≠ 1) :
    centLayer (CoreAssembly.conjClass K₀) u ≠ ⊤ := by
  have hZ : Subgroup.center G = ⊥ := InductionBridge.center_eq_bot_of_fstar_simple hS hnab
  have hYu : centLayer (CoreAssembly.conjClass K₀) u ≤ Subgroup.centralizer ({u} : Set G) :=
    centLayer_le fun L hL => hL.2
  intro htop
  apply hu1
  have hcent : u ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx : x ∈ Subgroup.centralizer ({u} : Set G) := hYu (htop ▸ Subgroup.mem_top x)
    exact Subgroup.mem_centralizer_singleton_iff.mp hx
  rw [hZ] at hcent
  exact (Subgroup.mem_bot).mp hcent

end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
