module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29Sc

public section

namespace CFSG.ComponentClassification.GSThmB.P29

open CFSG Subgroup DihedralGroup

theorem mem_conjugate_iff {G : Type*} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  rw [conjugate, Subgroup.mem_map_equiv]
  simp

namespace Model

variable {P : Type*} [Group P] {L : Subgroup P} {ι : P} {J : Subgroup P} {m : ℕ}
  (M : Model L ι J m)

theorem conj_iota_eq {c : P} (hc : c ∈ centralizer ({ι} : Set P)) : c * ι * c⁻¹ = ι := by
  rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]

include M in
theorem conj_mem_J {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) {x : P} (hx : x ∈ J) :
    c * x * c⁻¹ ∈ J := (M.normJ c hc x).mp hx

include M in
theorem conj_mem_cent {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) {x : P}
    (hx : x ∈ centralizer (J : Set P)) : c * x * c⁻¹ ∈ centralizer (J : Set P) := by
  rw [mem_centralizer_iff] at hx ⊢
  intro j hj
  have hj' : c⁻¹ * j * c⁻¹⁻¹ ∈ J := M.conj_mem_J (inv_mem hc) hj
  rw [inv_inv] at hj'
  have h := hx _ hj'
  calc j * (c * x * c⁻¹) = c * ((c⁻¹ * j * c) * x) * c⁻¹ := by group
    _ = c * (x * (c⁻¹ * j * c)) * c⁻¹ := by rw [h]
    _ = c * x * c⁻¹ * j := by group

include M in
theorem map_J {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) :
    J.map (MulAut.conj c).toMonoidHom = J := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have := M.conj_mem_J hc h
    rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at this
  · intro h
    have := M.conj_mem_J (inv_mem hc) h
    rwa [inv_inv] at this

include M in
theorem map_cent {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) :
    (centralizer (J : Set P)).map (MulAut.conj c).toMonoidHom = centralizer (J : Set P) := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  constructor
  · intro h
    have := M.conj_mem_cent hc h
    rwa [show c * (c⁻¹ * x * c) * c⁻¹ = x by group] at this
  · intro h
    have := M.conj_mem_cent (inv_mem hc) h
    rwa [inv_inv] at this

include M in
theorem conj_mem_sup_iff {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) (x : P) :
    c * x * c⁻¹ ∈ J ⊔ centralizer (J : Set P) ↔ x ∈ J ⊔ centralizer (J : Set P) := by
  have h := Subgroup.map_sup J (centralizer (J : Set P)) (MulAut.conj c).toMonoidHom
  rw [M.map_J hc, M.map_cent hc] at h
  conv_lhs => rw [← h]
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
    show c⁻¹ * (c * x * c⁻¹) * c = x by group]

@[expose] noncomputable def conj {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) :
    Model L ι J m where
  ρ := (MulAut.conj c).toMonoidHom.comp M.ρ
  t₀ := c * M.t₀ * c⁻¹
  two_le := M.two_le
  inj := (MulAut.conj c).injective.comp M.inj
  le_J x := M.conj_mem_J hc (M.le_J x)
  J_le_L := M.J_le_L
  t₀_mem := mul_mem (mul_mem hc.2 M.t₀_mem) (inv_mem hc.2)
  J_le := M.J_le
  normJ := M.normJ
  inf_cent := M.inf_cent
  comm x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h := M.comm x y
    calc c * M.ρ x * c⁻¹ * ((c * M.t₀ * c⁻¹)⁻¹ * (c * M.ρ y * c⁻¹) * (c * M.t₀ * c⁻¹)) =
        c * (M.ρ x * (M.t₀⁻¹ * M.ρ y * M.t₀)) * c⁻¹ := by group
      _ = c * ((M.t₀⁻¹ * M.ρ y * M.t₀) * M.ρ x) * c⁻¹ := by rw [h]
      _ = _ := by group
  gamma := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h := M.conj_mem_cent hc M.gamma
    convert h using 1
    group
  sr_not := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    intro h
    apply M.sr_not
    rw [← M.conj_mem_sup_iff hc]
    convert h using 1
    group
  iota := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc ι = c * ι * c⁻¹ := (conj_iota_eq hc.1).symm
      _ = c * (M.t₀⁻¹ * M.ρ (r (cc m)) * M.t₀) * c⁻¹ := by rw [← M.iota]
      _ = _ := by group
  sq := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hι : c * ι * c⁻¹ = ι := conj_iota_eq hc.1
    calc c * M.t₀ * c⁻¹ * (c * M.t₀ * c⁻¹) = c * (M.t₀ * M.t₀) * c⁻¹ := by group
      _ = c * (ι * M.ρ (r (cc m))) * c⁻¹ := by rw [M.sq]
      _ = (c * ι * c⁻¹) * (c * M.ρ (r (cc m)) * c⁻¹) := by group
      _ = _ := by rw [hι]
  not_conj g hg := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    intro h
    have hι : c⁻¹ * ι * c⁻¹⁻¹ = ι := conj_iota_eq (inv_mem hc.1)
    rw [inv_inv] at hι
    apply M.not_conj (c⁻¹ * g) (mul_mem (inv_mem hc.2) hg)
    calc c⁻¹ * g * ι * (c⁻¹ * g)⁻¹ = c⁻¹ * (g * ι * g⁻¹) * c := by group
      _ = c⁻¹ * (ι * (c * M.ρ (r (cc m)) * c⁻¹)) * c := by rw [h]
      _ = (c⁻¹ * ι * c) * M.ρ (r (cc m)) := by group
      _ = ι * M.ρ (r (cc m)) := by rw [hι]
  dvd_L := M.dvd_L
  not_dvd_L := M.not_dvd_L
  not_dvd_J := M.not_dvd_J

theorem conj_ρ {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) (x : DihedralGroup (2 ^ m)) :
    (M.conj hc).ρ x = c * M.ρ x * c⁻¹ := rfl

theorem conj_ρ₂ {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) (x : DihedralGroup (2 ^ m)) :
    (M.conj hc).ρ₂ x = c * M.ρ₂ x * c⁻¹ := by
  rw [ρ₂_apply, ρ₂_apply, conj_ρ]
  change (c * M.t₀ * c⁻¹)⁻¹ * (c * M.ρ x * c⁻¹) * (c * M.t₀ * c⁻¹) = _
  group

theorem T_conj {c : P} (hc : c ∈ centralizer ({ι} : Set P) ⊓ L) :
    (M.conj hc).T = M.T.map (MulAut.conj c).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    refine ⟨M.ρ a * M.ρ₂ b, ⟨(a, b), rfl⟩, ?_⟩
    show c * (M.ρ a * M.ρ₂ b) * c⁻¹ = (M.conj hc).ρ a * (M.conj hc).ρ₂ b
    rw [conj_ρ, conj_ρ₂]
    group
  · rintro ⟨_, ⟨⟨a, b⟩, rfl⟩, rfl⟩
    refine ⟨(a, b), ?_⟩
    show (M.conj hc).ρ a * (M.conj hc).ρ₂ b = c * (M.ρ a * M.ρ₂ b) * c⁻¹
    rw [conj_ρ, conj_ρ₂]
    group

end Model

end CFSG.ComponentClassification.GSThmB.P29
