module

public import CFSG.ClassicalInvolution.Asc77.AscE189Basic
public import CFSG.ClassicalInvolution.Asc77.AscT7AEStand
public import CFSG.ClassicalInvolution.Asc77.WP2Thm7b

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]

structure Hyp23Setting {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z : G) : Prop where
  stand : AscStand p f Ω K
  disconnected : ¬ DConnected Ω
  hz : IsUniqueInvolution K z
  hK' : K' ∈ twinSet Ω K
  hne : K' ≠ K
  perp : KPerp Ω K = {K, K'}

structure Hyp23bData {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G) : Prop where
  hW : W ∈ WSet Ω
  hS4 : MuIsoS4 Ω W
  hzW : z ∈ W
  hu : u ∈ K ⊔ K'
  huW : u ∈ W
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  he : Subgroup.closure {e} = W ⊓ centerIn (Subgroup.normalizer (W : Set G))
  he1 : e ≠ 1
  he2 : e * e = 1
  hg : g ∈ ⨆ R ∈ DSet Ω W, R
  hgt : g * z * g⁻¹ = u * e

variable {p f}

section Basic

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem Hyp23.setting (h : Hyp23 p f Ω K K' z) : Hyp23Setting p f Ω K K' z where
  stand := h.1.stand
  disconnected := h.1.disconnected
  hz := h.1.hz
  hK' := h.1.hK'
  hne := h.1.hne
  perp := h.2

theorem Hyp23Setting.hyp23 (h : Hyp23Setting p f Ω K K' z) (hcex : ¬ ConcOrTF4 G) :
    Hyp23 p f Ω K K' z :=
  ⟨{ stand := h.stand
     disconnected := h.disconnected
     hz := h.hz
     hK' := h.hK'
     hne := h.hne
     cex := hcex }, h.perp⟩

theorem Hyp23b.data (h : Hyp23b p f Ω K K' W z u e g) : Hyp23bData Ω K K' W z u e g where
  hW := h.hW
  hS4 := h.hS4
  hzW := h.hzW
  hu := h.hu
  huW := h.huW
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  he := h.he
  he1 := h.he1
  he2 := h.he2
  hg := h.hg
  hgt := h.hgt

theorem Hyp23bData.hyp23b (h : Hyp23bData Ω K K' W z u e g) (hs : Hyp23 p f Ω K K' z) :
    Hyp23b p f Ω K K' W z u e g where
  std := hs
  hW := h.hW
  hS4 := h.hS4
  hzW := h.hzW
  hu := h.hu
  huW := h.huW
  hu2 := h.hu2
  hu1 := h.hu1
  huz := h.huz
  he := h.he
  he1 := h.he1
  he2 := h.he2
  hg := h.hg
  hgt := h.hgt

theorem Hyp23Setting.twinSet_eq (h : Hyp23Setting p f Ω K K' z) : twinSet Ω K = {K, K'} := by
  ext L
  constructor
  · intro hL
    have hLperp : L ∈ KPerp Ω K :=
      mem_kPerp_of_twin h.stand.hyp hL.1 h.stand.mem (isUniqueInvolution_of_mem_twinSet h.hz hL)
        h.hz
    rw [h.perp] at hLperp
    exact hLperp
  · rintro (rfl | rfl)
    · exact mem_twinSet_self h.stand.mem h.hz
    · exact h.hK'

theorem Hyp23Setting.perp_of_twin (h : Hyp23Setting p f Ω K K' z) {L : Subgroup G}
    (hL : L ∈ twinSet Ω K) : KPerp Ω L = {K, K'} := by
  have h1 := (l6_3 p f h.stand.odd h.stand.five G Ω h.stand.hyp K h.stand.mem L hL).1
  rw [← h1]
  exact h.perp

theorem Hyp23Setting.isUniqueInvolution_of_mem_perp (h : Hyp23Setting p f Ω K K' z)
    {L J : Subgroup G} (hL : L ∈ twinSet Ω K) (hJ : J ∈ KPerp Ω L) : IsUniqueInvolution J z := by
  rw [h.perp_of_twin hL] at hJ
  rcases hJ with rfl | rfl
  · exact h.hz
  · exact isUniqueInvolution_of_mem_twinSet h.hz h.hK'

theorem Hyp23Setting.stdCent_of_twin (h : Hyp23Setting p f Ω K K' z) {H : Subgroup G}
    (hz : Subgroup.centralizer ({z} : Set G) ≤ H)
    (htwin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
      IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂,
        orderOf x = 4 → orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H) :
    StdCent Ω K H z where
  z_le := hz
  nonTwin := by
    intro L hL J hJ z' hz' hzz
    exfalso
    exact hzz (hz'.eq (h.isUniqueInvolution_of_mem_perp hL (Set.mem_insert_of_mem _ hJ)))
  twin := htwin

end Basic

end CFSG.ClassicalInvolution.Asc77
