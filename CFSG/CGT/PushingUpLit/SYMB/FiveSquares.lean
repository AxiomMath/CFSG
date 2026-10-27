module

public import CFSG.CGT.PushingUpLit.SYMB.FiveStruct

public section

namespace CFSG.CGT.PushingUpLit.SYMB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
  CFSG.CGT.PushingUpLit.BHS7
open scoped commutatorElement Pointwise

theorem A5_invol_conj : ∀ σ₀ σ : alternatingGroup (Fin 5), σ₀ ^ 2 = 1 → σ₀ ≠ 1 → σ ^ 2 = 1 →
    σ ≠ 1 → ∃ τ : alternatingGroup (Fin 5), τ * σ₀ * τ⁻¹ = σ := by
  decide +kernel

theorem mk_comm_of_commutator_mem {H : Type*} [Group H] {N : Subgroup H} [N.Normal] {a b : H}
    (h : ⁅a, b⁆ ∈ N) :
    (QuotientGroup.mk a : H ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a := by
  have h1 : ⁅(QuotientGroup.mk a : H ⧸ N), QuotientGroup.mk b⁆ = (1 : H ⧸ N) := by
    have h2 := map_commutatorElement (QuotientGroup.mk' N) a b
    have h3 : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h
    rw [h3] at h2
    exact h2.symm
  exact commutatorElement_eq_one_iff_mul_comm.1 h1

variable {Γ : Type} [Group Γ] [Finite Γ] {G T V : Subgroup Γ}
  {φ : ↥G →* Equiv.Perm (Fin 5)} {ψ : ↥V →* ↥(G6.coreMod 5)} {T' : Set (Equiv.Perm (Fin 5))}

namespace FiveCase

variable {S : SymSetting G T V 5 φ ψ T'} {E : Subgroup Γ}

theorem exists_sq_gen (h : FiveCase S E) :
    ∃ y ∈ E ⊓ Subgroup.centralizer (V : Set Γ),
      E ⊓ Subgroup.centralizer (V : Set Γ) ≤ Subgroup.zpowers y ⊔ ⁅V, E⁆ ∧ y ^ 2 ∈ ⁅V, E⁆ ∧
      ∀ (e : Γ) (he : e ∈ E), (φ ⟨e, h.join.le he⟩) ^ 2 = 1 → φ ⟨e, h.join.le he⟩ ≠ 1 →
        y⁻¹ * e ^ 2 ∈ ⁅V, E⁆ := by
  classical
  obtain ⟨e₀, he₀, h₀2, h₀1, hy, hKy, hy2⟩ := exists_ker_gen S h.join (by omega) h.isPGroup_K
  set N₁ : Subgroup Γ := ⁅V, E⁆ with hN₁
  set K : Subgroup Γ := E ⊓ Subgroup.centralizer (V : Set Γ) with hK
  have hKE : K ≤ E := inf_le_left
  have hN₁K : N₁ ≤ K := h.V₁_le_K
  have hN₁E : N₁ ≤ E := hN₁K.trans hKE
  have hKcomm : ⁅K, E⁆ ≤ N₁ := h.comm_K_E
  have hN₁G : G ≤ Subgroup.normalizer (N₁ : Set Γ) := comm_V_E_normal S h.normal
  have hKy' : K ≤ Subgroup.zpowers (e₀ ^ 2) ⊔ N₁ := hKy.trans (sup_le_sup_left hKcomm _)
  have hy2' : (e₀ ^ 2) ^ 2 ∈ N₁ := hKcomm hy2
  refine ⟨e₀ ^ 2, hy, hKy', hy2', ?_⟩
  intro e he h2 h1
  have hnormE : (N₁.subgroupOf E).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hgG : (g : Γ) ∈ G := h.join.le g.2
    have := (Subgroup.mem_normalizer_iff.mp (hN₁G hgG) (x : Γ)).mp hx
    simpa using this
  let q : ↥E →* ↥E ⧸ N₁.subgroupOf E := QuotientGroup.mk' (N₁.subgroupOf E)
  have hq1 : ∀ x : ↥E, q x = 1 ↔ (x : Γ) ∈ N₁ := fun x => by
    simp only [q, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hqcomm : ∀ a b : ↥E, ⁅(a : Γ), (b : Γ)⁆ ∈ N₁ → q a * q b = q b * q a := by
    intro a b hab
    exact mk_comm_of_commutator_mem (a := a) (b := b) (by rw [Subgroup.mem_subgroupOf]; exact hab)
  let E₀ : ↥E := ⟨e₀, he₀⟩
  let E1 : ↥E := ⟨e, he⟩
  obtain ⟨τ, hτ⟩ := A5_invol_conj ⟨φ ⟨e₀, h.join.le he₀⟩, h.join.map_mem_alt he₀⟩
    ⟨φ ⟨e, h.join.le he⟩, h.join.map_mem_alt he⟩ (Subtype.ext h₀2)
    (fun hh => h₀1 (congrArg Subtype.val hh)) (Subtype.ext h2)
    (fun hh => h1 (congrArg Subtype.val hh))
  have hτmem : (τ : Equiv.Perm (Fin 5)) ∈ imgG G φ E := by
    rw [h.join.img_eq_alt]
    exact τ.2
  obtain ⟨g, hgG, hgE, hgτ⟩ := mem_imgG.1 hτmem
  let Eg : ↥E := ⟨g, hgE⟩
  have hφe' : φ ⟨g * e₀ * g⁻¹, G.mul_mem (G.mul_mem hgG (h.join.le he₀)) (G.inv_mem hgG)⟩ =
      φ ⟨e, h.join.le he⟩ := by
    have e1 : (⟨g * e₀ * g⁻¹, G.mul_mem (G.mul_mem hgG (h.join.le he₀)) (G.inv_mem hgG)⟩ : ↥G) =
        ⟨g, hgG⟩ * ⟨e₀, h.join.le he₀⟩ * ⟨g, hgG⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv, hgτ]
    exact congrArg Subtype.val hτ
  have hκE : e⁻¹ * (g * e₀ * g⁻¹) ∈ E :=
    E.mul_mem (E.inv_mem he) (E.mul_mem (E.mul_mem hgE he₀) (E.inv_mem hgE))
  have hκK : e⁻¹ * (g * e₀ * g⁻¹) ∈ K := by
    refine ⟨hκE, ?_⟩
    have hκG : e⁻¹ * (g * e₀ * g⁻¹) ∈ G := h.join.le hκE
    have hker : e⁻¹ * (g * e₀ * g⁻¹) ∈ kerG G φ := by
      refine mem_kerG.2 ⟨hκG, ?_⟩
      have e1 : (⟨e⁻¹ * (g * e₀ * g⁻¹), hκG⟩ : ↥G) =
          ⟨e, h.join.le he⟩⁻¹ * ⟨g * e₀ * g⁻¹, G.mul_mem (G.mul_mem hgG (h.join.le he₀))
            (G.inv_mem hgG)⟩ := rfl
      rw [e1, map_mul, map_inv, hφe', inv_mul_cancel]
    exact FiveCase.ker_le_centralizer S hker
  let Ek : ↥E := ⟨e⁻¹ * (g * e₀ * g⁻¹), hκE⟩
  have hEk : E1 * Ek = Eg * E₀ * Eg⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, E1, Ek, Eg, E₀]
    group
  have hk_comm : q E1 * q Ek = q Ek * q E1 := by
    have h1' : ⁅(Ek : Γ), (E1 : Γ)⁆ ∈ ⁅K, E⁆ := Subgroup.commutator_mem_commutator hκK he
    exact (hqcomm Ek E1 (hKcomm h1')).symm
  have hk2 : q Ek * q Ek = 1 := by
    have hmulE : ((Subgroup.zpowers (e₀ ^ 2) ⊔ N₁ : Subgroup Γ) : Set Γ) =
        (Subgroup.zpowers (e₀ ^ 2) : Set Γ) * (N₁ : Set Γ) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((Subgroup.zpowers_le).2
        (h.normal.trans le_rfl |> fun _ => (hN₁G (h.join.le (E.pow_mem he₀ 2)))))
    have hκmem : e⁻¹ * (g * e₀ * g⁻¹) ∈ (Subgroup.zpowers (e₀ ^ 2) : Set Γ) * (N₁ : Set Γ) := by
      rw [← hmulE]
      exact hKy' hκK
    obtain ⟨x, hx, n, hn, hxn⟩ := Set.mem_mul.1 hκmem
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hxE : (e₀ ^ 2) ^ j ∈ E := E.zpow_mem (E.pow_mem he₀ 2) j
    have e2 : Ek = ⟨(e₀ ^ 2) ^ j, hxE⟩ * ⟨n, hN₁E hn⟩ := Subtype.ext hxn.symm
    have hq2 : q ⟨n, hN₁E hn⟩ = 1 := (hq1 _).2 hn
    have hqy : (q E₀ * q E₀) * (q E₀ * q E₀) = 1 := by
      have hh : q (E₀ * E₀ * (E₀ * E₀)) = 1 := (hq1 _).2 (by simpa [E₀, sq] using hy2')
      simpa [map_mul] using hh
    have e3 : q ⟨(e₀ ^ 2) ^ j, hxE⟩ = (q E₀ * q E₀) ^ j := by
      have : (⟨(e₀ ^ 2) ^ j, hxE⟩ : ↥E) = (E₀ * E₀) ^ j := by
        apply Subtype.ext
        simp [E₀, sq]
      rw [this, map_zpow, map_mul]
    rw [e2, map_mul, hq2, mul_one, e3]
    calc (q E₀ * q E₀) ^ j * (q E₀ * q E₀) ^ j = (q E₀ * q E₀) ^ (j + j) := (zpow_add _ j j).symm
      _ = (q E₀ * q E₀) ^ (2 * j) := by rw [two_mul]
      _ = ((q E₀ * q E₀) ^ (2 : ℤ)) ^ j := zpow_mul _ 2 j
      _ = 1 := by rw [zpow_two, hqy, one_zpow]
  have hg_comm : q Eg * (q E₀ * q E₀) = (q E₀ * q E₀) * q Eg := by
    have e1 : (E₀ * E₀ : ↥E) = ⟨e₀ ^ 2, E.pow_mem he₀ 2⟩ := by
      apply Subtype.ext
      simp [E₀, sq]
    rw [← map_mul, ← map_mul, ← map_mul, e1]
    have h1' : ⁅(((⟨e₀ ^ 2, E.pow_mem he₀ 2⟩ : ↥E)) : Γ), (Eg : Γ)⁆ ∈ ⁅K, E⁆ :=
      Subgroup.commutator_mem_commutator hy hgE
    have := hqcomm ⟨e₀ ^ 2, E.pow_mem he₀ 2⟩ Eg (hKcomm h1')
    exact this.symm
  have h3 : (q E1 * q Ek) * (q E1 * q Ek) = q E1 * q E1 := by
    calc (q E1 * q Ek) * (q E1 * q Ek) = q E1 * (q Ek * q E1) * q Ek := by group
      _ = q E1 * (q E1 * q Ek) * q Ek := by rw [← hk_comm]
      _ = q E1 * q E1 * (q Ek * q Ek) := by group
      _ = q E1 * q E1 := by rw [hk2, mul_one]
  have h4 : (q Eg * q E₀ * (q Eg)⁻¹) * (q Eg * q E₀ * (q Eg)⁻¹) = q E₀ * q E₀ := by
    calc (q Eg * q E₀ * (q Eg)⁻¹) * (q Eg * q E₀ * (q Eg)⁻¹)
        = q Eg * (q E₀ * q E₀) * (q Eg)⁻¹ := by group
      _ = (q E₀ * q E₀) * q Eg * (q Eg)⁻¹ := by rw [hg_comm]
      _ = q E₀ * q E₀ := by group
  have h5 : q E1 * q E1 = q E₀ * q E₀ := by
    have := congrArg q hEk
    rw [map_mul, map_mul, map_mul, map_inv] at this
    rw [← h3, this, h4]
  have h6 : q ⟨(e₀ ^ 2)⁻¹ * e ^ 2, E.mul_mem (E.inv_mem (E.pow_mem he₀ 2)) (E.pow_mem he 2)⟩ = 1 := by
    have e1 : (⟨(e₀ ^ 2)⁻¹ * e ^ 2, E.mul_mem (E.inv_mem (E.pow_mem he₀ 2)) (E.pow_mem he 2)⟩ : ↥E) =
        (E₀ * E₀)⁻¹ * (E1 * E1) := by
      apply Subtype.ext
      simp [E₀, E1, sq]
    rw [e1, map_mul, map_inv, map_mul, map_mul, h5, inv_mul_cancel]
  exact (hq1 _).1 h6

end FiveCase

end CFSG.CGT.PushingUpLit.SYMB
