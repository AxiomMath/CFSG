module

public import CFSG.ClassicalInvolution.Asc77.AscT7C2RConj
public import CFSG.ClassicalInvolution.Asc77.AscT7XFrame

public section

namespace CFSG.ClassicalInvolution.Asc77.S24

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_rep_conj [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u g : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (hg : g⁻¹ * z * g = u) {ρ ρ' : Thompson.Rep Ω W}
    (hρK : ρ.K = K) (hρ'K : ρ'.K = K') :
    ∃ ρ₃ : Thompson.Rep Ω W, ρ₃.K = conjSub g⁻¹ K := by
  have hst : AscStand p f Ω K := hs.stand
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hz : IsUniqueInvolution K z := hs.hz
  obtain ⟨g₀, hg₀, hg₀u⟩ := T7C2.exists_g0 hs hd
  have hn : g₀⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hg₀
  have hJ' : conjSub (g₀ * g⁻¹) K ∈ twinSet Ω K := by
    refine ⟨hΩ.conjInvariant _ K hK, z, hz, ?_⟩
    have h1 := hz.conj (g₀ * g⁻¹)
    have h2 : (g₀ * g⁻¹) * z * (g₀ * g⁻¹)⁻¹ = z := by
      calc (g₀ * g⁻¹) * z * (g₀ * g⁻¹)⁻¹ = g₀ * (g⁻¹ * z * g) * g₀⁻¹ := by group
        _ = g₀ * u * g₀⁻¹ := by rw [hg]
        _ = z := by rw [← hg₀u]; group
    rwa [h2] at h1
  have hKg : conjSub g⁻¹ K = conjSub g₀⁻¹ (conjSub (g₀ * g⁻¹) K) := by
    rw [← conjSub_mul, inv_mul_cancel_left]
  rw [hs.twinSet_eq] at hJ'
  rcases hJ' with h | h
  · exact ⟨T7D.conjRep hΩ hn ρ, by rw [hKg, h, ← hρK]; rfl⟩
  · exact ⟨T7D.conjRep hΩ hn ρ', by rw [hKg, h, ← hρ'K]; rfl⟩

theorem exists_frame24_conj [IsSimpleGroup G] {K K' : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u g : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (hg : g⁻¹ * z * g = u) :
    ∃ D : T7X.Frame24 p f Ω W, D.F.ρ.K = K ∧ D.F.ρ'.K = K' ∧ D.F.ρ.R = R ∧ D.F.ρ'.R = R' ∧
      D.F.z = z ∧ D.F.ρ₃.K = conjSub g⁻¹ K ∧ D.F.j = u := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have hW : W ∈ WSet Ω := hd.hW
  have c : Thompson.Ctx p f Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := T7D.exists_swap_equiv hs hW hd.hS4
  have hRsyl : IsSylow2In R K := T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK hd.hR.1 hd.hR.2.1
  have hR'syl : IsSylow2In R' K' :=
    T7C.isSylow2In_of_mem_RSet_of_le hp hΩ hK' hd.hR'.1 hd.hR'.2.1
  have hRD : R ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR.1 hd.hR.2.2
  have hR'D : R' ∈ DSet Ω W :=
    Thompson.mem_DSet_of_le_sylow hp hq hΩ hW hd.hWS hd.hR'.1 hd.hR'.2.2
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hp hq hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := T7D.exists_rep hp hq hΩ hW hK' hR'syl hR'D
  obtain ⟨ρ₃, hρ₃K⟩ := exists_rep_conj hs hd hg hρK hρ'K
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hu : IsUniqueInvolution ρ₃.K u := by
    have := hz.conj g⁻¹
    rw [inv_inv, hg] at this
    rw [hρ₃K]
    exact this
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  have hKgK : conjSub g⁻¹ K ≠ K := fun h => hd.hu.2.2.2.2 (by
    have hu' : IsUniqueInvolution (conjSub g⁻¹ K) u := hρ₃K ▸ hu
    rw [h] at hu'
    exact (hz.eq hu').symm)
  have hKgK' : conjSub g⁻¹ K ≠ K' := fun h => hd.hu.2.2.2.2 (by
    have hu' : IsUniqueInvolution (conjSub g⁻¹ K) u := hρ₃K ▸ hu
    rw [h] at hu'
    exact (hz'.eq hu').symm)
  have hne₁ : ρ.K ≠ ρ₃.K := by
    rw [hρK, hρ₃K]
    exact hKgK.symm
  have hne₂ : ρ'.K ≠ ρ₃.K := by
    rw [hρ'K, hρ₃K]
    exact hKgK'.symm
  have hn₁ : ρ₃.K ∉ omegaNbr Ω ρ.K := fun h => by
    have h1 : ρ₃.K ∈ KPerp Ω K := by rw [← hρK]; exact Or.inr h
    rw [hs.perp, hρ₃K] at h1
    rcases h1 with h2 | h2
    · exact hKgK h2
    · exact hKgK' h2
  have hn₂ : ρ₃.K ∉ omegaNbr Ω ρ'.K := fun h => by
    have h1 : ρ₃.K ∈ KPerp Ω K' := by rw [← hρ'K]; exact Or.inr h
    rw [hs.perp_of_twin hs.hK', hρ₃K] at h1
    rcases h1 with h2 | h2
    · exact hKgK h2
    · exact hKgK' h2
  have hac : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := fun h =>
    hn₁ (c.omega_of_comm ρ ρ₃ hne₁ (congrArg Subtype.val h))
  have hbc : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := fun h =>
    hn₂ (c.omega_of_comm ρ' ρ₃ hne₂ (congrArg Subtype.val h))
  let F : T7E.Frame4 Ω W := ⟨ρ, ρ', ρ₃, z, u, hzρ, hzρ', hu, hρnbr, hρnbr', hne₁, hne₂, hn₁, hn₂,
    fun h => hac (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm),
    fun h => hbc (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)⟩
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁, r₂, r₃, t₁, t₂, t₃, s₁, s₂, s₃⟩ := F.exists_gens c
  obtain ⟨m, hm, o₁, o₂, o₃, z₁, z₂, z₃⟩ := F.orders c h₁ h₂ h₃
  refine ⟨{
    c := c, F := F, φ := e, hφ := he, hab := hab, hcomm := hcommQ, hac := hac,
    x₁ := x₁, x₂ := x₂, x₃ := x₃, m := m, hm := hm, h₁ := h₁, h₂ := h₂, h₃ := h₃,
    r₁ := r₁, r₂ := r₂, r₃ := r₃, t₁ := t₁, t₂ := t₂, t₃ := t₃, s₁ := s₁, s₂ := s₂, s₃ := s₃,
    o₁ := o₁, o₂ := o₂, o₃ := o₃, z₁ := z₁, z₂ := z₂, z₃ := z₃,
    hgen := F.W_le_closure c he hab hcommQ hac h₁ h₂ h₃ r₂ r₃ t₃ },
    hρK, hρ'K, hρR, hρ'R, rfl, hρ₃K, rfl⟩

end CFSG.ClassicalInvolution.Asc77.S24
