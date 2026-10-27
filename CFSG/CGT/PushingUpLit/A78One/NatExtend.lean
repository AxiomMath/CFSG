module

public import CFSG.CGT.PushingUpLit.T2K.Setup
public import CFSG.CGT.PushingUpLit.BHS.BlockStatements
public import CFSG.CGT.PushingUpLit.T2K.Basic

public section

namespace CFSG.CGT.PushingUpLit.A78One

open CFSG CFSG.Open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.T2K

variable {G : Type} [Group G]

structure NatExt (L P : Subgroup G) : Prop where
  le : blockU L ≤ P
  comm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  dec : ∀ p ∈ P, ∃ u ∈ blockU L, ∃ c ∈ P ⊓ Subgroup.centralizer (L : Set G), p = u * c
  cent : L ⊓ Subgroup.centralizer (P : Set G) = oTwoIn L

namespace NatExt

variable {L P : Subgroup G} {n : ℕ}

open Classical in
noncomputable def psi' (D : NatData L n) (u : G) : Multiplicative (Fin 2 → GaloisField 2 n) :=
  if h : u ∈ blockU L then D.ψ ⟨u, h⟩ else 1

theorem psi'_of_mem (D : NatData L n) {u : G} (hu : u ∈ blockU L) :
    psi' D u = D.ψ ⟨u, hu⟩ := by
  unfold psi'
  simp [hu]

theorem psi'_mul (D : NatData L n) {u v : G} (hu : u ∈ blockU L) (hv : v ∈ blockU L) :
    psi' D (u * v) = psi' D u * psi' D v := by
  rw [psi'_of_mem D hu, psi'_of_mem D hv, psi'_of_mem D ((blockU L).mul_mem hu hv)]
  exact map_mul D.ψ ⟨u, hu⟩ ⟨v, hv⟩

theorem psi'_eq (D : NatData L n) {u u' c c' : G} (hu : u ∈ blockU L) (hu' : u' ∈ blockU L)
    (hc : c ∈ Subgroup.centralizer (L : Set G)) (hc' : c' ∈ Subgroup.centralizer (L : Set G))
    (h : u * c = u' * c') : psi' D u = psi' D u' := by
  have h1 : u'⁻¹ * u = c' * c⁻¹ := by
    calc u'⁻¹ * u = u'⁻¹ * (u * c) * c⁻¹ := by group
      _ = u'⁻¹ * (u' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have h2 : u'⁻¹ * u ∈ blockZ L := by
    refine ⟨(blockU L).mul_mem ((blockU L).inv_mem hu') hu, ?_⟩
    rw [h1]
    exact (Subgroup.centralizer (L : Set G)).mul_mem hc'
      ((Subgroup.centralizer (L : Set G)).inv_mem hc)
  have h3 := (D.ψ_ker ⟨u'⁻¹ * u, (blockU L).mul_mem ((blockU L).inv_mem hu') hu⟩).2 h2
  have h4 : psi' D (u'⁻¹ * u) = psi' D u'⁻¹ * psi' D u := psi'_mul D ((blockU L).inv_mem hu') hu
  rw [psi'_of_mem D ((blockU L).mul_mem ((blockU L).inv_mem hu') hu)] at h4
  rw [h3] at h4
  have h5 : psi' D u'⁻¹ = (psi' D u')⁻¹ := by
    rw [psi'_of_mem D ((blockU L).inv_mem hu'), psi'_of_mem D hu']
    exact map_inv D.ψ ⟨u', hu'⟩
  rw [h5] at h4
  exact (inv_mul_eq_one.1 h4.symm).symm

noncomputable def uOf (h : NatExt L P) (p : ↥P) : G := Classical.choose (h.dec p p.2)

theorem uOf_spec (h : NatExt L P) (p : ↥P) :
    uOf h p ∈ blockU L ∧ ∃ c ∈ P ⊓ Subgroup.centralizer (L : Set G), (p : G) = uOf h p * c :=
  Classical.choose_spec (h.dec p p.2)

noncomputable def psiP (D : NatData L n) (h : NatExt L P) :
    ↥P →* Multiplicative (Fin 2 → GaloisField 2 n) :=
  MonoidHom.mk' (fun p => psi' D (uOf h p)) (by
    intro p q
    obtain ⟨hu, c, hc, hpc⟩ := uOf_spec h p
    obtain ⟨hv, d, hd, hqd⟩ := uOf_spec h q
    obtain ⟨hw, e, he, hpqe⟩ := uOf_spec h (p * q)
    have hcv : c * uOf h q = uOf h q * c := h.comm c hc.1 _ (h.le hv)
    have hpq : ((p * q : ↥P) : G) = (uOf h p * uOf h q) * (c * d) := by
      rw [Subgroup.coe_mul, hpc, hqd]
      calc uOf h p * c * (uOf h q * d) = uOf h p * (c * uOf h q) * d := by group
        _ = uOf h p * (uOf h q * c) * d := by rw [hcv]
        _ = uOf h p * uOf h q * (c * d) := by group
    have h1 := psi'_eq D hw ((blockU L).mul_mem hu hv) he.2
      ((Subgroup.centralizer (L : Set G)).mul_mem hc.2 hd.2) (hpqe.symm.trans hpq)
    show psi' D (uOf h (p * q)) = psi' D (uOf h p) * psi' D (uOf h q)
    rw [h1, psi'_mul D hu hv])

theorem psiP_eq (D : NatData L n) (h : NatExt L P) {p : ↥P} {u c : G} (hu : u ∈ blockU L)
    (hc : c ∈ Subgroup.centralizer (L : Set G)) (hpc : (p : G) = u * c) :
    psiP D h p = psi' D u := by
  obtain ⟨hu0, c0, hc0, hp0⟩ := uOf_spec h p
  exact psi'_eq D hu0 hu hc0.2 hc (hp0.symm.trans hpc)

theorem psiP_surjective (D : NatData L n) (h : NatExt L P) : Function.Surjective (psiP D h) := by
  intro v
  obtain ⟨⟨u, hu⟩, rfl⟩ := D.ψ_surj v
  refine ⟨⟨u, h.le hu⟩, ?_⟩
  rw [psiP_eq D h hu (Subgroup.one_mem _) (by simp), psi'_of_mem D hu]
  
theorem psiP_ker (D : NatData L n) (h : NatExt L P) :
    (psiP D h).ker = (P ⊓ Subgroup.centralizer (L : Set G)).subgroupOf P := by
  ext p
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  obtain ⟨hu, c, hc, hpc⟩ := uOf_spec h p
  rw [psiP_eq D h hu hc.2 hpc, psi'_of_mem D hu]
  have hZ := D.ψ_ker ⟨uOf h p, hu⟩
  constructor
  · intro h1
    refine ⟨p.2, ?_⟩
    have h2 : uOf h p ∈ blockZ L := hZ.1 h1
    rw [hpc]
    exact (Subgroup.centralizer (L : Set G)).mul_mem h2.2 hc.2
  · rintro ⟨-, h1⟩
    apply hZ.2
    refine ⟨hu, ?_⟩
    have h3 : uOf h p = p * c⁻¹ := by rw [hpc]; group
    have hmem : uOf h p ∈ Subgroup.centralizer (L : Set G) := by
      rw [h3]
      exact (Subgroup.centralizer (L : Set G)).mul_mem h1
        ((Subgroup.centralizer (L : Set G)).inv_mem hc.2)
    exact hmem

theorem isNatSL_of_natExt (D : NatData L n) (h : NatExt L P) : IsNatSL L P n := by
  refine ⟨D.φ, psiP D h, D.φ_surj, ?_, psiP_surjective D h, psiP_ker D h, ?_⟩
  · ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, h.cent]
    exact D.φ_ker l
  · intro e w hw
    obtain ⟨hu, c, hc, hwc⟩ := uOf_spec h w
    have hec : (e : G) * c * (e : G)⁻¹ = c := by
      have h0 := Subgroup.mem_centralizer_iff.1 hc.2 e e.2
      calc (e : G) * c * (e : G)⁻¹ = c * e * (e : G)⁻¹ := by rw [h0]
        _ = c := by group
    have hu' : (e : G) * uOf h w * (e : G)⁻¹ ∈ blockU L :=
      conj_mem_blockU (Subgroup.le_normalizer e.2) hu
    have hew : (e : G) * w * (e : G)⁻¹ = ((e : G) * uOf h w * (e : G)⁻¹) * c := by
      rw [hwc]
      calc (e : G) * (uOf h w * c) * (e : G)⁻¹
          = ((e : G) * uOf h w * (e : G)⁻¹) * ((e : G) * c * (e : G)⁻¹) := by group
        _ = ((e : G) * uOf h w * (e : G)⁻¹) * c := by rw [hec]
    have h1 : psiP D h ⟨(e : G) * w * (e : G)⁻¹, hw⟩ =
        psi' D ((e : G) * uOf h w * (e : G)⁻¹) := psiP_eq D h hu' hc.2 hew
    have h2 := D.ψ_conj e ⟨uOf h w, hu⟩ hu'
    have h3 : psiP D h w = D.ψ ⟨uOf h w, hu⟩ := by
      rw [psiP_eq D h hu hc.2 hwc, psi'_of_mem D hu]
    rw [h1, psi'_of_mem D hu', h3]
    exact h2

end NatExt

end CFSG.CGT.PushingUpLit.A78One
