module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4M2
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4P2a
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y4Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {s : Setting3 G L}
  {e : Setting3.Ext s}

private theorem y4_phi_eq_one_of_mem_B (c : Ctx4 s e) {b : G} (hb : b ∈ s.fr.B) :
    f3phi s b = 1 := by
  have hbt : b * s.t = s.t * b :=
    s3_comm_t_of_mem_L s (s3_S_le_L s (s3_B_le_S s hb))
  show b * s.t * b⁻¹ * s.t⁻¹ = 1
  rw [hbt]
  group

theorem y4_S2_moves_V (c : Ctx4 s e) {x : G} (hxS2 : x ∈ y4S2 s) (hxM : x ∉ M2 s) :
    ∃ v ∈ cen s.fr.B, x * v * x⁻¹ ≠ v := by
  have hH := c.toF33
  have hxS2' : x ∈ s.fr.S ⊔ M2 s := by rw [sup_comm]; exact hxS2
  have hnorm : ∀ t ∈ s.fr.S, ∀ m ∈ M2 s, t * m * t⁻¹ ∈ M2 s :=
    fun t ht m hm => y54_M2_inv hH t (f3_T_le_N hH (s3_S_le_T s ht)) m hm
  obtain ⟨y, hyS, m, hmM2, hxym⟩ :=
    mem_sup_of_normalizes (T := s.fr.S) (C := M2 s) hnorm x hxS2'
  have hyB : y ∉ s.fr.B := by
    intro hyb
    apply hxM
    rw [hxym]
    exact (M2 s).mul_mem (y54_B_le_M2 s hyb) hmM2
  by_contra hcon
  have hcon' : ∀ v ∈ cen s.fr.B, x * v * x⁻¹ = v := by
    intro v hv
    by_contra hne
    exact hcon ⟨v, hv, hne⟩
  have hycent : ∀ v ∈ cen s.fr.B, y * v * y⁻¹ = v := by
    intro v hv
    have hx := hcon' v hv
    have hmv : m * v * m⁻¹ = v := y4_C2_cent_V c (y4_M2_le_C2 hH hmM2) hv
    have hfac : x * v * x⁻¹ = y * v * y⁻¹ := by
      rw [hxym]
      calc y * m * v * (y * m)⁻¹ = y * (m * v * m⁻¹) * y⁻¹ := by group
        _ = y * v * y⁻¹ := by rw [hmv]
    rwa [hfac] at hx
  have hmax : IsMaximalIn s.fr.S s.fr.B := hH.hLF.fact14.2.2.1.2.2.1
  have hlt : s.fr.B < s.fr.B ⊔ zpowers y := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro heq
    have hy : y ∈ s.fr.B ⊔ zpowers y :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
    rw [← heq] at hy
    exact hyB hy
  have hSB : s.fr.B ⊔ zpowers y = s.fr.S :=
    hmax.2 (s.fr.B ⊔ zpowers y) hlt
      (sup_le (s3_B_le_S s) (Subgroup.zpowers_le.mpr hyS))
  have hVle : cen s.fr.B ≤ cen s.fr.S := by
    intro v hv
    have hvB : v ∈ s.fr.B := s3_cenB_le_B s hv
    have vcommB : v ∈ Subgroup.centralizer (s.fr.B : Set G) := (Subgroup.mem_inf.mp hv).2
    refine Subgroup.mem_inf.mpr ⟨s3_B_le_S s hvB, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hg' : g ∈ s.fr.B ⊔ zpowers y := by rwa [hSB]
    have hle : s.fr.B ⊔ zpowers y ≤ Subgroup.centralizer ({v} : Set G) := by
      rw [sup_le_iff]
      refine ⟨?_, ?_⟩
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff.mp hz]
        exact (Subgroup.mem_centralizer_iff.mp vcommB b hb).symm
      · intro g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hyv : y * v = v * y := by
          have h := hycent v hv
          calc y * v = (y * v * y⁻¹) * y := by group
            _ = v * y := by rw [h]
        exact (Subgroup.centralizer ({v} : Set G)).zpow_mem
          (Subgroup.mem_centralizer_iff.mpr (fun z hz => by
            rw [Set.mem_singleton_iff.mp hz]
            exact hyv.symm)) k
    have hmem := hle hg'
    rw [Subgroup.mem_centralizer_iff] at hmem
    exact (hmem v (by simp)).symm
  have hVle_z : cen s.fr.B ≤ zpowers s.fr.z := by
    intro v hv
    have hvcen : v ∈ cen s.fr.S := hVle hv
    rwa [c.hA.cen_S] at hvcen
  have hcard : Nat.card ↥(cen s.fr.B) ≤ 2 := by
    calc Nat.card ↥(cen s.fr.B) ≤ Nat.card ↥(zpowers s.fr.z) :=
          Subgroup.card_le_of_le hVle_z
      _ = orderOf s.fr.z := Nat.card_zpowers s.fr.z
      _ = 2 := s3_z_order s c.hA
  have h4 := y4_card_V hH
  omega

theorem y4_card_centM2_le (c : Ctx4 s e) {x : G} (hxS2 : x ∈ y4S2 s) (hxM : x ∉ M2 s) :
    Nat.card ↥(centEl (M2 s) x) ≤ 2 * Nat.card ↥(centEl s.fr.B x) := by
  have hH := c.toF33
  have hnot := y4_S2_moves_V c hxS2 hxM
  have hxS2' : x ∈ s.fr.S ⊔ M2 s := by rw [sup_comm]; exact hxS2
  have hnorm : ∀ t ∈ s.fr.S, ∀ m ∈ M2 s, t * m * t⁻¹ ∈ M2 s :=
    fun t ht m hm => y54_M2_inv hH t (f3_T_le_N hH (s3_S_le_T s ht)) m hm
  obtain ⟨y, hyS, m, hmM2, hxym⟩ :=
    mem_sup_of_normalizes (T := s.fr.S) (C := M2 s) hnorm x hxS2'
  have hyt : y * s.t = s.t * y := s3_comm_t_of_mem_L s (s3_S_le_L s hyS)
  obtain ⟨f, hf, -, hfker⟩ := f3_phiHom hH
  have phi_mul : ∀ a ∈ s.C₂, ∀ b ∈ s.C₂, f3phi s (a * b) = f3phi s a * f3phi s b := by
    intro a ha b hb
    have h := congrArg (fun z : ↥(cen s.fr.B) => (z : G)) (map_mul f ⟨a, ha⟩ ⟨b, hb⟩)
    simpa [hf] using h
  let K : Subgroup G := centEl (M2 s) x
  have hKC2 : K ≤ s.C₂ := fun k hk => y4_M2_le_C2 hH (Subgroup.mem_inf.mp hk).1
  have hmem : ∀ k : ↥K,
      f (Subgroup.inclusion hKC2 k) ∈ (centEl (cen s.fr.B) x).subgroupOf (cen s.fr.B) := by
    intro k
    rw [Subgroup.mem_subgroupOf]
    have hkM2 : (k : G) ∈ M2 s := (Subgroup.mem_inf.mp k.2).1
    have hkcent : (k : G) ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp k.2).2
    have hcomm : x * (k : G) = (k : G) * x :=
      Subgroup.mem_centralizer_iff.mp hkcent x (by simp)
    have hxconj : x * (k : G) * x⁻¹ = (k : G) := by
      rw [hcomm]; group
    have hyconj : y * (m * (k : G) * m⁻¹) * y⁻¹ = (k : G) := by
      have h2 := hxconj
      rw [hxym] at h2
      calc y * (m * (k : G) * m⁻¹) * y⁻¹ = y * m * (k : G) * (y * m)⁻¹ := by group
        _ = (k : G) := h2
    have hmk : f3phi s (m * (k : G) * m⁻¹) = f3phi s (k : G) := by
      have h1 : m * (k : G) * m⁻¹ = ⁅m, (k : G)⁆ * (k : G) := by
        rw [commutatorElement_def]; group
      rw [h1]
      have hmC : m ∈ s.C₂ := y4_M2_le_C2 hH hmM2
      have hkC : (k : G) ∈ s.C₂ := hKC2 k.2
      have hb : ⁅m, (k : G)⁆ ∈ s.fr.B := y4_C2_comm c m hmC (k : G) hkC
      have hbC : ⁅m, (k : G)⁆ ∈ s.C₂ := y4_M2_le_C2 hH (y54_B_le_M2 s hb)
      rw [phi_mul ⁅m, (k : G)⁆ hbC (k : G) hkC,
        y4_phi_eq_one_of_mem_B c hb, one_mul]
    have hconj := f3_phi_conj s hyt (m * (k : G) * m⁻¹)
    rw [hyconj, hmk] at hconj
    have hkval : ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) = f3phi s (k : G) :=
      hf (Subgroup.inclusion hKC2 k)
    have hmv : m * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * m⁻¹ =
        ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) :=
      y4_C2_cent_V c (y4_M2_le_C2 hH hmM2) ((f (Subgroup.inclusion hKC2 k)).2)
    have hyact : y * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * y⁻¹ =
        ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) := by
      rw [hkval]
      exact hconj.symm
    have hxact : x * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * x⁻¹ =
        ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) := by
      rw [hxym]
      calc y * m * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * (y * m)⁻¹ =
            y * (m * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * m⁻¹) * y⁻¹ :=
              by group
        _ = y * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * y⁻¹ := by rw [hmv]
        _ = ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) := hyact
    refine Subgroup.mem_inf.mpr ⟨(f (Subgroup.inclusion hKC2 k)).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    calc x * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) =
          (x * ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * x⁻¹) * x := by group
      _ = ((f (Subgroup.inclusion hKC2 k) : ↥(cen s.fr.B)) : G) * x := by rw [hxact]
  let ψ : ↥K →* ↥(cen s.fr.B) := f.comp (Subgroup.inclusion hKC2)
  have hmem_ker : ∀ k : ↥K, k ∈ ψ.ker ↔ (k : G) ∈ f3P s := by
    intro k
    rw [MonoidHom.mem_ker]
    change f (Subgroup.inclusion hKC2 k) = 1 ↔ (k : G) ∈ f3P s
    constructor
    · intro hk
      have := (hfker (Subgroup.inclusion hKC2 k)).mp hk
      simpa [Subgroup.coe_inclusion] using this
    · intro hk
      exact (hfker (Subgroup.inclusion hKC2 k)).mpr
        (by simpa [Subgroup.coe_inclusion] using hk)
  have hKinf : K ⊓ f3P s = centEl s.fr.B x := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgK, hgP⟩ := Subgroup.mem_inf.mp hg
      have hgM2 : g ∈ M2 s := (Subgroup.mem_inf.mp hgK).1
      have hgcent : g ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hgK).2
      have hgB : g ∈ s.fr.B := by
        have h : g ∈ M2 s ⊓ f3P s := Subgroup.mem_inf.mpr ⟨hgM2, hgP⟩
        rwa [y4_M2_inf_P c] at h
      exact Subgroup.mem_inf.mpr ⟨hgB, hgcent⟩
    · intro g hg
      obtain ⟨hgB, hgcent⟩ := Subgroup.mem_inf.mp hg
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_inf.mpr ⟨y54_B_le_M2 s hgB, hgcent⟩, Subgroup.mem_sup_left hgB⟩
  have hkermap : ψ.ker.map K.subtype = K ⊓ f3P s := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_map] at hg
      obtain ⟨k, hkker, rfl⟩ := hg
      exact Subgroup.mem_inf.mpr ⟨k.2, (hmem_ker k).mp hkker⟩
    · intro g hg
      obtain ⟨hgK, hgP⟩ := Subgroup.mem_inf.mp hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hgK⟩, ?_, rfl⟩
      exact (hmem_ker ⟨g, hgK⟩).mpr hgP
  have hcard_ker : Nat.card ψ.ker = Nat.card ↥(centEl s.fr.B x) := by
    rw [← Subgroup.card_subtype K ψ.ker, hkermap, hKinf]
  have hrange_le : ψ.range ≤ (centEl (cen s.fr.B) x).subgroupOf (cen s.fr.B) := by
    rintro y ⟨k, rfl⟩
    exact hmem k
  have hcardS : Nat.card ↥((centEl (cen s.fr.B) x).subgroupOf (cen s.fr.B)) =
      Nat.card ↥(centEl (cen s.fr.B) x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : centEl (cen s.fr.B) x ≤ cen s.fr.B)).toEquiv
  have hrange : Nat.card ψ.range ≤ 2 := by
    calc Nat.card ψ.range ≤
          Nat.card ↥((centEl (cen s.fr.B) x).subgroupOf (cen s.fr.B)) :=
          Subgroup.card_le_of_le hrange_le
      _ = Nat.card ↥(centEl (cen s.fr.B) x) := hcardS
      _ ≤ 2 := y4_card_centV_le c hnot
  change Nat.card ↥K ≤ 2 * Nat.card ↥(centEl s.fr.B x)
  calc Nat.card ↥K = Nat.card ψ.ker * Nat.card ψ.range :=
        (Subgroup.card_ker_mul_card_range ψ).symm
    _ ≤ Nat.card ↥(centEl s.fr.B x) * 2 := Nat.mul_le_mul (le_of_eq hcard_ker) hrange
    _ = 2 * Nat.card ↥(centEl s.fr.B x) := by ring

end CFSG.OddStandard.HigherRank.YamadaG23
