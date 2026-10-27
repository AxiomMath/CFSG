module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance

section Open

variable {G G' : Type*} [Group G] [Group G'] {H K M : Subgroup G}

theorem isSubnormal_trans_open (h : CFSG.Open.IsSubnormal H K) (h' : CFSG.Open.IsSubnormal K M) :
    CFSG.Open.IsSubnormal H M :=
  h.trans h'

theorem le_of_isSubnormal_open (h : CFSG.Open.IsSubnormal H K) : H ≤ K :=
  h.le

theorem isSubnormal_map_open (f : G →* G') (h : CFSG.Open.IsSubnormal H K) :
    CFSG.Open.IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem isSubnormal_subgroupOf_open (h : CFSG.Open.IsSubnormal H K) :
    (H.subgroupOf K).IsSubnormal :=
  h.subgroupOf

end Open

theorem isSubnormal_map_centralizer {Y : Type*} [Group Y] {n : ℕ}
    (φ : Y →* Equiv.Perm (Fin n)) (hrange : φ.range = alternatingGroup (Fin n))
    (hker : φ.ker ≤ Subgroup.center Y) (α : MulAut Y) (σ : Equiv.Perm (Fin n))
    (hφ : ∀ y, φ (α y) = σ * φ y * σ⁻¹) {J : Subgroup Y}
    (hJ : CFSG.Open.IsSubnormal J (Lemma510Ns.fixSub α)) :
    J.map φ ≤ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))) ∧
      ((J.map φ).subgroupOf
        (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))))).IsSubnormal := by
  set X := Lemma510Ns.fixSub α with hXdef
  set Cs := Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))) with hCs
  set T : Subgroup Y := Cs.comap φ with hT
  have hXT : X ≤ T := by
    intro y hy
    have hy' : α y = y := hy
    have h1 := hφ y
    rw [hy'] at h1
    show φ y ∈ Cs
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc φ y * σ = (σ * φ y * σ⁻¹) * σ := by rw [← h1]
      _ = σ * φ y := by group
  have hN : (X.subgroupOf T).Normal := by
    constructor
    intro x hx t
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxα : α (x : Y) = x := hx
    have ht : φ (t : Y) ∈ Cs := t.2
    have hcomm : σ * φ t = φ t * σ := (Subgroup.mem_centralizer_singleton_iff.1 ht).symm
    have hz : (t : Y)⁻¹ * α t ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ]
      rw [hcomm]
      group
    have hzc := Subgroup.mem_center_iff.1 (hker hz)
    show α ((t : Y) * x * (t : Y)⁻¹) = (t : Y) * x * (t : Y)⁻¹
    rw [map_mul, map_mul, map_inv, hxα]
    generalize hzdef : (t : Y)⁻¹ * α t = z at hzc
    have hαt : α (t : Y) = (t : Y) * z := by rw [← hzdef]; group
    rw [hαt]
    have hx' : (x : Y) * z = z * x := hzc x
    calc (t : Y) * z * x * ((t : Y) * z)⁻¹ = (t : Y) * (z * x) * z⁻¹ * (t : Y)⁻¹ := by group
      _ = (t : Y) * (x * z) * z⁻¹ * (t : Y)⁻¹ := by rw [hx']
      _ = (t : Y) * x * (t : Y)⁻¹ := by group
  have h1 : CFSG.Open.IsSubnormal X T := .step hXT hN (.refl T)
  have h3 := isSubnormal_map_open φ (isSubnormal_trans_open hJ h1)
  have hTm : T.map φ = Cs ⊓ alternatingGroup (Fin n) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hy, ?_⟩
      rw [← hrange]
      exact ⟨y, rfl⟩
    · rintro ⟨hxC, hxA⟩
      rw [← hrange] at hxA
      obtain ⟨y, rfl⟩ := hxA
      exact ⟨y, hxC, rfl⟩
  have hCn : CFSG.Open.IsSubnormal (Cs ⊓ alternatingGroup (Fin n)) Cs := by
    refine .step inf_le_left ?_ (.refl Cs)
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨(g * x * g⁻¹).2, (inferInstance : (alternatingGroup (Fin n)).Normal).conj_mem _ hx.2 _⟩
  rw [hTm] at h3
  have h4 := isSubnormal_trans_open h3 hCn
  exact ⟨le_of_isSubnormal_open h4, isSubnormal_subgroupOf_open h4⟩

end CFSG.HardMathSupport.Solomon.Coordinator
