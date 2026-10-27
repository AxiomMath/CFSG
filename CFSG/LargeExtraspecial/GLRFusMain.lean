module

public import CFSG.LargeExtraspecial.GLRFusCase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

namespace Mixed

variable {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} {k : G} {α β : S.Qt}

theorem swap (hM : Mixed S X A B k α β) : Mixed S X B A k β α :=
  ⟨hM.pair.symm, hM.five_le, hM.le_Mbar, hM.conj_mem, hM.conj_ne, hM.mem_B, hM.mem_A,
    hM.ne_zero_B, hM.ne_zero_A, by rw [hM.cl_eq, add_comm]⟩

theorem mem_span_of_polar_kerB (hM : Mixed S X A B k α β) {b : S.Qt} (hb : b ∈ B)
    (hK : ∀ u ∈ kerB A β, polar S.q u b = 0) : b ∈ Submodule.span (ZMod 2) ({β} : Set S.Qt) := by
  obtain ⟨a₀, ha₀, ha₀β⟩ := hM.exists_a₀
  set c := polar S.q a₀ b
  have h0 : b - c • β = 0 := by
    refine hM.pair.eq_zero_of_polar (B.sub_mem hb (B.smul_mem _ hM.mem_B)) fun a ha => ?_
    have hk := sub_mem_kerB ha₀ ha₀β ha
    have hkβ : polar S.q (a - polar S.q a β • a₀) β = 0 := hk.2
    have e1 : a = (a - polar S.q a β • a₀) + polar S.q a β • a₀ := by abel
    rw [e1, polar_sub_right, polar_add_left, polar_add_left, polar_smul_right, polar_smul_right,
      polar_smul_left, polar_smul_left, hK _ hk, hkβ, ha₀β]
    simp only [c, smul_eq_mul]
    ring
  rw [sub_eq_zero.mp h0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self β)

theorem mem_root_or (hM : Mixed S X A B k α β) {e : S.O} (he : e ∈ S.Lbar k ⊓ X) :
    e ∈ rootGroup A α ∨ e ∈ rootGroup B β := by
  obtain ⟨a₀, ha₀, ha₀β⟩ := hM.exists_a₀
  obtain ⟨heα, heβ⟩ := hM.fix_of_mem he
  set E := (e : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE
  by_cases hw : E a₀ - a₀ ∈ Submodule.span (ZMod 2) ({α} : Set S.Qt)
  · left
    refine ⟨heα, fun a ha => ?_⟩
    have hk := sub_mem_kerB ha₀ ha₀β ha
    have e1 : E a - a = (E (a - polar S.q a β • a₀) - (a - polar S.q a β • a₀)) +
        polar S.q a β • (E a₀ - a₀) := by
      rw [map_sub, map_smul, smul_sub]; abel
    rw [e1]
    exact Submodule.add_mem _ (hM.apply_K he hk) (Submodule.smul_mem _ _ hw)
  · right
    have hK : ∀ u ∈ kerB A β, E u = u := by
      intro u hu
      rcases mem_span_singleton_iff.mp (hM.apply_K he hu) with h0 | h1
      · exact sub_eq_zero.mp h0
      · exact (hM.not_both he ha₀ ha₀β hu
          ((sub_eq_iff_eq_add.mp h1).trans (add_comm _ _)) hw).elim
    refine ⟨heβ, fun b hb => ?_⟩
    refine hM.mem_span_of_polar_kerB (B.sub_mem (hM.pair.apply_B e he.2 b hb) hb) fun u hu => ?_
    have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup e.2 u b
    rw [← hE, hK u hu] at h1
    rw [polar_sub_right, h1, sub_self]

theorem le_root (hM : Mixed S X A B k α β) :
    S.Lbar k ⊓ X ≤ rootGroup A α ∨ S.Lbar k ⊓ X ≤ rootGroup B β := by
  by_contra hc
  push Not at hc
  obtain ⟨x, hx, hxA⟩ := Set.not_subset.mp hc.1
  obtain ⟨y, hy, hyB⟩ := Set.not_subset.mp hc.2
  have hxB := (hM.mem_root_or hx).resolve_left hxA
  have hyA := (hM.mem_root_or hy).resolve_right hyB
  rcases hM.mem_root_or ((S.Lbar k ⊓ X).mul_mem hx hy) with h | h
  · exact hxA (by simpa using (rootGroup A α).mul_mem h ((rootGroup A α).inv_mem hyA))
  · exact hyB (by simpa using (rootGroup B β).mul_mem ((rootGroup B β).inv_mem hxB) h)

theorem not_le_rootGroup (hM : Mixed S X A B k α β) (hEX : S.Lbar k ≤ X)
    (hE : S.Lbar k ≤ rootGroup A α) : False := by
  have h5 := hM.five_le
  set R := rootGroup A α ⊓ X
  have hcard : Nat.card R ≤ Nat.card (S.Lbar k) :=
    (hM.pair.card_rootGroup_le hM.mem_A hM.ne_zero_A).trans
      (S.card_Lbar_ge hM.conj_mem hM.conj_ne)
  have hLeq : S.Lbar k = R := Subgroup.eq_of_le_of_card_ge (le_inf hE hEX) hcard
  obtain ⟨p, hpX, hpα, hpβ⟩ := hM.pair.exists_fix_move (by omega) hM.mem_A hM.mem_B hM.ne_zero_B
  obtain ⟨m, hm⟩ := hM.le_Mbar hpX
  have hinv : ∀ v, ((p⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((p : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
    fun v => by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have hpα' : ((p⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) α = α := by
    conv_lhs => rw [← hpα]
    exact hinv α
  have hL : S.Lbar ((m : G) * k) = S.Lbar k := by
    rw [S.s12_Lbar_mul m k, hLeq, hm]
    apply le_antisymm
    · rintro _ ⟨r, hr, rfl⟩
      exact hM.pair.conj_mem_rootGroup hpX hpα hr
    · intro r hr
      refine ⟨p⁻¹ * r * p, ?_, ?_⟩
      · have := hM.pair.conj_mem_rootGroup (X.inv_mem hpX) hpα' hr
        rwa [inv_inv] at this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hbQ : ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ∈ S.QG := by
    rw [S.s12_mul_conj_z]; exact S.conj_mem_QG m.2 hM.conj_mem
  have hbne : ((m : G) * k) * S.z * ((m : G) * k)⁻¹ ≠ S.z := by
    rw [S.s12_mul_conj_z]
    intro h'
    apply hM.conj_ne
    calc k * S.z * k⁻¹ = (m : G)⁻¹ * ((m : G) * (k * S.z * k⁻¹) * (m : G)⁻¹) * m := by group
      _ = (m : G)⁻¹ * S.z * (m : G)⁻¹⁻¹ := by rw [h']; group
      _ = S.z := S.s12_conj_z_of_mem_M (S.M.inv_mem m.2)
  have hcl := cl_eq_of_Lbar_eq hbQ hbne hM.conj_mem hM.conj_ne (by omega) hL
  rw [S.s12_mul_conj_z, ← S.ρ_cl m hM.conj_mem, hm, hM.cl_eq, map_add, hpα] at hcl
  exact hpβ (add_left_cancel hcl)

theorem not_mem_outer (hM : Mixed S X A B k α β) (hidx : X.relIndex S.Mbar = 2)
    (hσ : ∀ σ ∈ S.Mbar, σ ∉ X →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B)
    {e₁ : S.O} (he₁ : e₁ ∈ S.Lbar k) (he₁X : e₁ ∉ X) : False := by
  have h5 := hM.five_le
  set E₁ := (e₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hE₁
  have hmap := hσ e₁ (S.Lbar_le_Mbar k he₁) he₁X
  have hsq : ∀ v, E₁ (E₁ v) = v := fun v => by
    rw [hE₁, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul, Lbar_mul_self hM.conj_mem he₁]; rfl
  have hAB : ∀ a ∈ A, E₁ a ∈ B := fun a ha => hmap ▸ Submodule.mem_map_of_mem ha
  have hBA : ∀ b ∈ B, E₁ b ∈ A := by
    intro b hb
    rw [← hmap] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    change E₁ (E₁ a) ∈ A
    rw [hsq]; exact ha
  have hfix := hM.Lbar_fix he₁
  rw [map_add] at hfix
  have hd : E₁ β - α ∈ A ⊓ B := by
    refine ⟨A.sub_mem (hBA β hM.mem_B) hM.mem_A, ?_⟩
    have : E₁ β - α = β - E₁ α := by rw [sub_eq_sub_iff_add_eq_add, add_comm, hfix, add_comm]
    rw [this]
    exact B.sub_mem hM.mem_B (hAB α hM.mem_A)
  rw [hM.pair.inf_eq, Submodule.mem_bot, sub_eq_zero] at hd
  have he₁α : E₁ α = β := by rw [← hd, hsq]
  have hboth : ∀ e ∈ S.Lbar k ⊓ X, e ∈ rootGroup A α ⊓ rootGroup B β := by
    intro e he
    obtain ⟨heα, heβ⟩ := hM.fix_of_mem he
    have hc : ∀ v, (e : S.Qt ≃ₗ[ZMod 2] S.Qt) (E₁ v) = E₁ ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) v) := by
      intro v
      have := congrArg (fun f : S.O => (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
        (Lbar_comm hM.conj_mem he.1 he₁)
      simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using this
    have hspan : ∀ {γ δ : S.Qt}, E₁ γ = δ → ∀ v ∈ Submodule.span (ZMod 2) ({γ} : Set S.Qt),
        E₁ v ∈ Submodule.span (ZMod 2) ({δ} : Set S.Qt) := by
      intro γ δ hγ v hv
      rcases mem_span_singleton_iff.mp hv with rfl | rfl
      · rw [map_zero]; exact Submodule.zero_mem _
      · rw [hγ]; exact Submodule.mem_span_singleton_self _
    rcases hM.le_root with hA | hB
    · refine ⟨hA he, heβ, fun b hb => ?_⟩
      have h1 := (hA he).2 (E₁ b) (hBA b hb)
      have e2 : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) b - b =
          E₁ ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) (E₁ b) - E₁ b) := by
        rw [map_sub, ← hc, hsq]
      rw [e2]
      exact hspan he₁α _ h1
    · refine ⟨⟨heα, fun a ha => ?_⟩, hB he⟩
      have h1 := (hB he).2 (E₁ a) (hAB a ha)
      have e2 : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) a - a =
          E₁ ((e : S.Qt ≃ₗ[ZMod 2] S.Qt) (E₁ a) - E₁ a) := by
        rw [map_sub, ← hc, hsq]
      rw [e2]
      exact hspan hd _ h1
  have hle : S.Lbar k ⊓ X ≤ rootGroup A α ⊓ rootGroup B β ⊓ X :=
    fun e he => ⟨hboth e he, he.2⟩
  have h2 := (Subgroup.card_le_of_le hle).trans
    (hM.pair.card_rootGroup_inf_le (β := β) hM.mem_A hM.ne_zero_A)
  have hrel : X.relIndex (S.Lbar k) ≤ 2 :=
    calc X.relIndex (S.Lbar k) ≤ X.relIndex S.Mbar :=
          Subgroup.relIndex_le_of_le_right (S.Lbar_le_Mbar k) (by rw [hidx]; norm_num)
      _ = 2 := hidx
  have hmul : Nat.card (S.Lbar k ⊓ X : Subgroup S.O) * X.relIndex (S.Lbar k) =
      Nat.card (S.Lbar k) := by
    have := Subgroup.card_mul_index (X.subgroupOf (S.Lbar k))
    have hc : Nat.card (X.subgroupOf (S.Lbar k)) = Nat.card (S.Lbar k ⊓ X : Subgroup S.O) := by
      rw [← Subgroup.inf_subgroupOf_right,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : X ⊓ S.Lbar k ≤ _)).toEquiv,
        inf_comm]
    rw [hc] at this
    exact this
  have hge := S.card_Lbar_ge hM.conj_mem hM.conj_ne
  have h16 : 2 ^ 4 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Nat.card (S.Lbar k) ≤ 4 := by
    rw [← hmul]
    calc Nat.card (S.Lbar k ⊓ X : Subgroup S.O) * X.relIndex (S.Lbar k) ≤ 2 * 2 :=
          Nat.mul_le_mul h2 hrel
      _ = 4 := by norm_num
  omega

end Mixed

theorem fusion {X : Subgroup S.O} {A B : Submodule (ZMod 2) S.Qt} (h : Pair S X A B)
    (h5 : 5 ≤ S.width) (hXM : X ≤ S.Mbar) (hidx : X.relIndex S.Mbar = 2)
    (hσ : ∀ σ ∈ S.Mbar, σ ∉ X →
      A.map ((σ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) = B)
    (k : G) (hk : k * S.z * k⁻¹ ∈ S.QG) :
    S.cl (k * S.z * k⁻¹) ∈ A ∨ S.cl (k * S.z * k⁻¹) ∈ B := by
  by_cases hz : k * S.z * k⁻¹ = S.z
  · left
    rw [hz, S.cl_z]
    exact A.zero_mem
  have hv : S.cl (k * S.z * k⁻¹) ∈ A ⊔ B := by rw [h.sup_eq]; exact Submodule.mem_top
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.mp hv
  by_cases hα0 : α = 0
  · right
    rw [← hαβ, hα0, zero_add]
    exact hβ
  by_cases hβ0 : β = 0
  · left
    rw [← hαβ, hβ0, add_zero]
    exact hα
  exfalso
  have hM : Mixed S X A B k α β := ⟨h, h5, hXM, hk, hz, hα, hβ, hα0, hβ0, hαβ.symm⟩
  by_cases hEX : S.Lbar k ≤ X
  · have hE : S.Lbar k ⊓ X = S.Lbar k := inf_eq_left.mpr hEX
    rcases hM.le_root with hA | hB
    · exact hM.not_le_rootGroup hEX (hE ▸ hA)
    · exact hM.swap.not_le_rootGroup hEX (hE ▸ hB)
  · obtain ⟨e₁, he₁, he₁X⟩ := Set.not_subset.mp hEX
    exact hM.not_mem_outer hidx hσ he₁ he₁X

end CFSG.LargeExtraspecial.GLR
