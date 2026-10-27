module

public import CFSG.CGT.PushingUpLit.T2K.Cohomology

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.Quasithin.JonesParshall
open scoped commutatorElement

variable {G : Type} [Group G] {L M : Subgroup G} {n : ℕ}

variable [Finite G]

@[expose] noncomputable def kap (D : NatData L n) (u : G)
    (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) : Fin 2 → Fq n :=
  D.ψe (delta u (D.sec g : G))

omit [Finite G] in
theorem kappa_def (D : NatData L n) (u : G) (g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)) :
    kap D u g = D.ψe (delta u (D.sec g : G)) := rfl

theorem kappa_mul (h : NatBlock L n) (D : NatData L n) (hLM : L ≤ M)
    (hMN : M ≤ Subgroup.normalizer (L : Set G)) {u : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (g g' : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    kap D u (g * g') = kap D u g +
      ((g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (kap D u g') := by
  set l : ↥L := D.sec g
  set l' : ↥L := D.sec g'
  set o : ↥L := D.sec (g * g') * (l * l')⁻¹ with ho
  have hoφ : D.φ o = 1 := by
    rw [ho, map_mul, map_inv, map_mul, D.φ_sec, D.φ_sec, D.φ_sec, mul_inv_cancel]
  have hoO : (o : G) ∈ oTwoIn L := (D.φ_ker o).1 hoφ
  have e1 : (D.sec (g * g') : G) = o * ((l : G) * l') := by
    simp only [ho, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hV1 : delta u (l : G) ∈ blockU L := h.delta_mem hMN hu l.2
  have hV2 : delta u (l' : G) ∈ blockU L := h.delta_mem hMN hu l'.2
  have hV3 : delta u ((l : G) * l') ∈ blockU L :=
    h.delta_mem hMN hu (mul_mem l.2 l'.2)
  have hZo : delta u (o : G) ∈ blockZ L := h.delta_oTwoIn_mem hLM hMN hu hoO
  have hconj : (o : G) * delta u ((l : G) * l') * (o : G)⁻¹ = delta u ((l : G) * l') := by
    have := blockU_comm_of_short h.short _ hV3 _ hoO
    rw [← this, mul_inv_cancel_right]
  have hmem : (l : G) * delta u (l' : G) * (l : G)⁻¹ ∈ blockU L :=
    conj_mem_blockU (Subgroup.le_normalizer l.2) hV2
  rw [kappa_def, kappa_def, kappa_def]
  rw [e1, delta_mul, hconj, D.ψe_mul (blockZ_le_blockU L hZo) hV3,
    (D.ψe_eq_zero_iff (blockZ_le_blockU L hZo)).2 hZo, zero_add, delta_mul,
    D.ψe_mul hV1 hmem, D.ψe_conj l.2 hV2]
  have : D.φ ⟨(l : G), l.2⟩ = g := D.φ_sec g
  rw [this]

theorem kappa_mem_Z1A (h : NatBlock L n) (D : NatData L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    kap D u ∈ Z1A (mu2 (F := GaloisField 2 n)) := fun g g' => by
  rw [kappa_mul h D hLM hMN hu g g', mu2_apply]

theorem kappa_mul_left (h : NatBlock L n) (D : NatData L n) (hMN : M ≤ Subgroup.normalizer (L : Set G)) {u u' : G}
    (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (hu' : u' ∈ M ⊓ Subgroup.centralizer (blockU L : Set G))
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    kap D (u * u') g = kap D u g + kap D u' g := by
  have hl : (D.sec g : G) ∈ L := (D.sec g).2
  have hV1 : delta u (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu hl
  have hV2 : delta u' (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu' hl
  have hc : u'⁻¹ * delta u (D.sec g : G) * u' = delta u (D.sec g : G) := by
    have := Subgroup.mem_centralizer_iff.1 hu'.2 _ hV1
    rw [mul_assoc, this, inv_mul_cancel_left]
  rw [kappa_def, kappa_def, kappa_def]
  rw [delta_mul_left, hc, D.ψe_mul hV1 hV2]

theorem kappa_apply (h : NatBlock L n) (D : NatData L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) {l : G} (hl : l ∈ L) :
    kap D u (D.φ ⟨l, hl⟩) = D.ψe (delta u l) := by
  set g := D.φ ⟨l, hl⟩ with hg
  set o : ↥L := ⟨l, hl⟩ * (D.sec g)⁻¹ with ho
  have hoφ : D.φ o = 1 := by
    rw [ho, map_mul, map_inv, D.φ_sec, hg, mul_inv_cancel]
  have hoO : (o : G) ∈ oTwoIn L := (D.φ_ker o).1 hoφ
  have e1 : l = o * (D.sec g : G) := by
    simp only [ho, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hV1 : delta u (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu (D.sec g).2
  have hZo : delta u (o : G) ∈ blockZ L := h.delta_oTwoIn_mem hLM hMN hu hoO
  have hconj : (o : G) * delta u (D.sec g : G) * (o : G)⁻¹ = delta u (D.sec g : G) := by
    have := blockU_comm_of_short h.short _ hV1 _ hoO
    rw [← this, mul_inv_cancel_right]
  rw [kappa_def]
  rw [e1, delta_mul, hconj, D.ψe_mul (blockZ_le_blockU L hZo) hV1,
    (D.ψe_eq_zero_iff (blockZ_le_blockU L hZo)).2 hZo, zero_add]

theorem kappa_eq_zero_iff (h : NatBlock L n) (D : NatData L n) (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    {u : G} (hu : u ∈ M ⊓ Subgroup.centralizer (blockU L : Set G)) :
    kap D u = 0 ↔ u ∈ Subgroup.centralizer (L : Set G) := by
  constructor
  · intro h0
    have hZ : ∀ l ∈ L, delta u l ∈ blockZ L := by
      intro l hl
      set g := D.φ ⟨l, hl⟩ with hg
      set o : ↥L := ⟨l, hl⟩ * (D.sec g)⁻¹ with ho
      have hoφ : D.φ o = 1 := by
        rw [ho, map_mul, map_inv, D.φ_sec, hg, mul_inv_cancel]
      have hoO : (o : G) ∈ oTwoIn L := (D.φ_ker o).1 hoφ
      have e1 : l = o * (D.sec g : G) := by
        simp only [ho, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have hV1 : delta u (D.sec g : G) ∈ blockU L := h.delta_mem hMN hu (D.sec g).2
      have hZo : delta u (o : G) ∈ blockZ L := h.delta_oTwoIn_mem hLM hMN hu hoO
      have hconj : (o : G) * delta u (D.sec g : G) * (o : G)⁻¹ = delta u (D.sec g : G) := by
        have := blockU_comm_of_short h.short _ hV1 _ hoO
        rw [← this, mul_inv_cancel_right]
      have hZ1 : delta u (D.sec g : G) ∈ blockZ L :=
        (D.ψe_eq_zero_iff hV1).1 (by simpa [kappa_def] using congrFun h0 g)
      rw [e1, delta_mul, hconj]
      exact (blockZ L).mul_mem hZo hZ1
    have hx : u⁻¹ ∈ Subgroup.normalizer (L : Set G) := hMN (M.inv_mem hu.1)
    have key := comm_eq_one_of_perfect h.perfect hx
      (fun l hl => NatBlock.blockZ_le_centralizer L (by
        have := hZ l hl
        simpa [delta, commutatorElement_def, mul_assoc] using this))
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    have h1 := key l hl
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    have h2 : u⁻¹ * l = l * u⁻¹ := h1
    calc l * u = u * (u⁻¹ * l) * u⁻¹⁻¹ := by group
      _ = u * (l * u⁻¹) * u⁻¹⁻¹ := by rw [h2]
      _ = u * l := by group
  · intro hc
    funext g
    rw [kappa_def, Pi.zero_apply]
    have : delta u (D.sec g : G) = 1 := by
      have hh := Subgroup.mem_centralizer_iff.1 hc _ (D.sec g).2
      calc delta u (D.sec g : G) = u⁻¹ * ((D.sec g : G) * u) * (D.sec g : G)⁻¹ := by
            simp only [delta]; group
        _ = u⁻¹ * (u * (D.sec g : G)) * (D.sec g : G)⁻¹ := by rw [hh]
        _ = 1 := by group
    rw [this, D.ψe_one]

omit [Finite G] in
theorem kappa_blockU (D : NatData L n) {v : G} (hv : v ∈ blockU L)
    (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    kap D v g = coboundaryA (mu2 (F := GaloisField 2 n)) (D.ψe v) g := by
  have hl : (D.sec g : G) ∈ L := (D.sec g).2
  have hw : (D.sec g : G) * v * (D.sec g : G)⁻¹ ∈ blockU L :=
    conj_mem_blockU (Subgroup.le_normalizer hl) hv
  rw [kappa_def]
  have e : delta v (D.sec g : G) = v⁻¹ * ((D.sec g : G) * v * (D.sec g : G)⁻¹) := by
    simp only [delta]
    group
  rw [e, D.ψe_mul (inv_mem hv) hw, D.ψe_inv hv, D.ψe_conj hl hv, coboundaryA_apply, mu2_apply]
  have : D.φ ⟨(D.sec g : G), hl⟩ = g := D.φ_sec g
  rw [this]
  abel

end CFSG.CGT.PushingUpLit.T2KR
