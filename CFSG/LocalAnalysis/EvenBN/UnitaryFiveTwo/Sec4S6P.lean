module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6M
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6L

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer

theorem X₂sub_inf_Fsub : X₂sub ⊓ Fsub = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg2, hgF⟩
  obtain ⟨a, ha⟩ := mem_X₂sub.1 hg2
  obtain ⟨-, -, h10, -⟩ := mem_Fsub.1 hgF
  have ha0 : a = 0 := by
    have : mat g 1 0 = a := by rw [ha]; rfl
    rw [← this]
    exact h10
  subst ha0
  refine Subgroup.mem_bot.2 (ext_mat ?_)
  rw [ha, mat_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [x₂Mat]

theorem card_X₂sub_sup_Fsub : 2 ^ 6 ≤ Nat.card ↥(X₂sub ⊔ Fsub) := by
  have hinj : Function.Injective (fun p : X₂sub × Fsub =>
      (⟨(p.1 : SU52) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ :
        ↥(X₂sub ⊔ Fsub))) := by
    rintro ⟨⟨x, hx⟩, ⟨f, hf⟩⟩ ⟨⟨x', hx'⟩, ⟨f', hf'⟩⟩ h
    have h1 : x * f = x' * f' := congrArg Subtype.val h
    have h2 : x'⁻¹ * x = f' * f⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * f) * f⁻¹ := by group
        _ = x'⁻¹ * (x' * f') * f⁻¹ := by rw [h1]
        _ = f' * f⁻¹ := by group
    have h3 : x'⁻¹ * x ∈ X₂sub ⊓ Fsub :=
      ⟨X₂sub.mul_mem (X₂sub.inv_mem hx') hx, h2 ▸ Fsub.mul_mem hf' (Fsub.inv_mem hf)⟩
    rw [X₂sub_inf_Fsub, Subgroup.mem_bot] at h3
    have h4 : x = x' := by
      calc x = x' * (x'⁻¹ * x) := by group
        _ = x' := by rw [h3, mul_one]
    subst h4
    have h5 : f = f' := mul_left_cancel h1
    subst h5
    rfl
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, card_X₂sub, card_Fsub] at this
  norm_num at this
  exact this

variable {G : Type} [Group G] [Finite G] {d : Data G} {K₀ : Subgroup G}

theorem Data.X₂_sup_F_eq (d : Data G) : d.X₂ ⊔ d.F = d.pull (X₂sub ⊔ Fsub) :=
  (d.pull_sup X₂sub Fsub).symm

theorem Data.card_X₂_sup_F (d : Data G) : 2 ^ 6 ≤ Nat.card ↥(d.X₂ ⊔ d.F) := by
  rw [Data.X₂_sup_F_eq, d.card_pull]
  exact card_X₂sub_sup_Fsub

theorem Data.X₂_sup_F_le_S (d : Data G) : d.X₂ ⊔ d.F ≤ d.S :=
  sup_le (d.pull_mono X₂sub_le_Ssub) (d.F_le_A₂.trans d.A₂_le_S)

theorem Data.X₂_sup_F_le_K₃ (d : Data G) : d.X₂ ⊔ d.F ≤ d.K₃ :=
  sup_le (d.pull_mono X₂sub_le_K₃sub') d.F_le_K₃

theorem Data.X₂_sup_F_le_centralizer_e₂ (d : Data G) :
    d.X₂ ⊔ d.F ≤ centralizer ({d.e₂} : Set G) := by
  rw [Data.X₂_sup_F_eq, ← Ssub_inf_centralizer_e₂SU]
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ centralizer ({e₂SU} : Set SU52) := hx.2
  refine mem_centralizer_singleton_iff.2 ?_
  have := mem_centralizer_singleton_iff.1 hx'
  show d.ι x * d.ι e₂SU = d.ι e₂SU * d.ι x
  rw [← map_mul, ← map_mul, this]

theorem eq_of_le_of_isPGroup_of_card {X : Type*} [Group X] [Finite X] {P T : Subgroup X}
    (hPT : P ≤ T) (hT : IsPGroup 2 ↥T) (hP : 2 ^ 6 ≤ Nat.card ↥P)
    (hX : Nat.card X ∣ 25920) : P = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
  have hTdvd : Nat.card ↥T ∣ 25920 := (Subgroup.card_subgroup_dvd_card T).trans hX
  have hn6 : n ≤ 6 := by
    by_contra hlt
    have h7 : 2 ^ 7 ∣ 25920 :=
      (pow_dvd_pow 2 (by omega : 7 ≤ n)).trans (hn ▸ hTdvd)
    norm_num at h7
  have hcard : Nat.card ↥T ≤ Nat.card ↥P := by
    rw [hn]
    exact (Nat.pow_le_pow_right (by norm_num) hn6).trans hP
  exact Subgroup.eq_of_le_of_card_ge hPT hcard

theorem Data.IsUnitaryFactor.tc_factor (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) :
    d.IsUnitaryFactor (d.tc K₀) where
  lieModel := CFSG.Blueprint.LieModel.of_mulEquiv
    (Subgroup.equivMapOfInjective K₀ (MulAut.conj d.t).toMonoidHom (MulAut.conj d.t).injective)
    hf.lieModel
  K_eq := by
    show d.K = d.tc K₀ ⊔ d.tc (d.tc K₀)
    rw [h.tc_tc, sup_comm]
    exact hf.K_eq_tc
  comm := by
    show ⁅d.tc K₀, d.tc (d.tc K₀)⁆ = ⊥
    rw [h.tc_tc, Subgroup.commutator_comm]
    exact hf.comm
  inf := by
    show d.tc K₀ ⊓ d.tc (d.tc K₀) = ⊥
    rw [h.tc_tc, inf_comm]
    exact hf.inf

@[expose] noncomputable def Data.proj0 (hf : d.IsUnitaryFactor K₀) : ↥(K₀ ⊔ d.tc K₀) →* ↥K₀ :=
  KProd.projA K₀ (d.tc K₀) hf.comm_elem hf.inf_tc

theorem Data.theta_mem_sup (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) (k : ↥K₀) :
    Data.theta h hf k ∈ K₀ ⊔ d.tc K₀ := by
  rw [Data.theta_apply]
  refine mul_mem (mem_sup_left k.2) (mem_sup_right ?_)
  rw [h.mem_tc, h.t_conj_conj]
  exact k.2

theorem Data.proj0_mul (hf : d.IsUnitaryFactor K₀) {a b : G} (ha : a ∈ K₀) (hb : b ∈ d.tc K₀) :
    (Data.proj0 hf ⟨a * b, mul_mem (mem_sup_left ha) (mem_sup_right hb)⟩ : G) = a := by
  have : (⟨a * b, mul_mem (mem_sup_left ha) (mem_sup_right hb)⟩ : ↥(K₀ ⊔ d.tc K₀)) =
      KProd.prodEquivSup K₀ (d.tc K₀) hf.comm_elem hf.inf_tc (⟨a, ha⟩, ⟨b, hb⟩) :=
    Subtype.ext (by rw [KProd.prodEquivSup_apply])
  rw [this]
  exact congrArg Subtype.val (KProd.projA_prod _ _ _ _ ⟨a, ha⟩ ⟨b, hb⟩)

theorem Data.proj0_theta (h : d.Hyp) (hf : d.IsUnitaryFactor K₀) (k : ↥K₀) :
    Data.proj0 hf ⟨Data.theta h hf k, Data.theta_mem_sup h hf k⟩ = k := by
  have hb : d.t * (k : G) * d.t ∈ d.tc K₀ := (h.mem_tc).2 (by rw [h.t_conj_conj]; exact k.2)
  have : (⟨Data.theta h hf k, Data.theta_mem_sup h hf k⟩ : ↥(K₀ ⊔ d.tc K₀)) =
      KProd.prodEquivSup K₀ (d.tc K₀) hf.comm_elem hf.inf_tc (k, ⟨d.t * k * d.t, hb⟩) :=
    Subtype.ext (by rw [KProd.prodEquivSup_apply]; exact Data.theta_apply h hf k)
  rw [this]
  exact KProd.projA_prod _ _ _ _ k _

section Comp



variable (h : d.Hyp) (hKU : d.KUnitary)

include h hKU in
theorem Data.card_K₀_dvd (hf : d.IsUnitaryFactor K₀) : Nat.card ↥K₀ ∣ 25920 := by
  have h1 : Nat.card ↥K₀ = Nat.card ↥(Data.theta h hf).range :=
    Nat.card_congr (MonoidHom.ofInjective (Data.theta_injective h hf)).toEquiv
  rw [h1, Data.range_theta h hKU hf, Data.K₃, d.card_pull]
  exact card_K₃sub_dvd

include h hKU in
theorem Data.Hyp.theta_component_mem (hf : d.IsUnitaryFactor K₀) {m a b : G}
    (hm : m ∈ d.D₁ ⊓ centralizer ({d.e₂} : Set G)) (ha : a ∈ K₀) (hb : b ∈ d.tc K₀)
    (hmab : m = a * b) : a * (d.t * a * d.t) ∈ d.X₂ ⊔ d.F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' : Subgroup G := K₀ ⊔ d.tc K₀ with hK'
  set M : Subgroup G := d.D₁ ⊓ centralizer ({d.e₂} : Set G) with hM
  have hKK : d.K = K' := hf.K_eq_tc
  have hMK : M ≤ K' := by
    rw [← hKK]
    exact h.M_le_K (h.Y_le_K' hKU) (Data.Hyp.K₃_le_K hKU)
  have hQK : d.X₂ ⊔ d.F ≤ K' := by
    rw [← hKK]
    exact d.X₂_sup_F_le_K₃.trans (Data.Hyp.K₃_le_K hKU)
  have hX₂M : d.X₂ ≤ M := fun x hx =>
    Subgroup.mem_inf.2 ⟨h.A₁_le_D₁ (d.pull_mono X₂sub_le_A₁sub hx),
      d.X₂_sup_F_le_centralizer_e₂ (mem_sup_left hx)⟩
  have hFnorm : ∀ f ∈ d.F, ∀ m' ∈ M, f * m' * f⁻¹ ∈ M := by
    intro f hf' m' hm'
    have hfS : f ∈ d.S := d.A₂_le_S (d.F_le_A₂ hf')
    have hfXW : f ∈ d.XW := h.NHS_le_XW (Subgroup.mem_inf.2
      ⟨le_normalizer hfS, h.L_le_H (d.pull_le_L _ hfS)⟩)
    have hfC : f ∈ centralizer ({d.e₂} : Set G) :=
      d.X₂_sup_F_le_centralizer_e₂ (mem_sup_right hf')
    refine Subgroup.mem_inf.2 ⟨h.conj_mem_D₁ hfXW (Subgroup.mem_inf.1 hm').1, ?_⟩
    exact (centralizer ({d.e₂} : Set G)).mul_mem
      ((centralizer ({d.e₂} : Set G)).mul_mem hfC (Subgroup.mem_inf.1 hm').2)
      ((centralizer ({d.e₂} : Set G)).inv_mem hfC)
  set π := Data.proj0 hf with hπ
  set Mπ : Subgroup ↥K₀ := (M.subgroupOf K').map π with hMπ
  set Qπ : Subgroup ↥K₀ := ((d.X₂ ⊔ d.F).subgroupOf K').map π with hQπ
  set Q₀ : Subgroup ↥K₀ := (d.X₂ ⊔ d.F).comap (Data.theta h hf) with hQ₀
  have hMp : IsPGroup 2 ↥M := (IsPGroup.of_card h.card_D₁).to_le inf_le_left
  have hMπp : IsPGroup 2 ↥Mπ := (hMp.comap_subtype (K := K')).map π
  have hSp : IsPGroup 2 ↥d.S := IsPGroup.of_card d.card_S
  have hQp : IsPGroup 2 ↥(d.X₂ ⊔ d.F) := hSp.to_le d.X₂_sup_F_le_S
  have hQπp : IsPGroup 2 ↥Qπ := (hQp.comap_subtype (K := K')).map π
  have hQN : Qπ ≤ normalizer (Mπ : Set ↥K₀) := by
    rw [hQπ, Subgroup.map_le_iff_le_comap,
      Subgroup.subgroupOf_sup (le_sup_left.trans hQK) (le_sup_right.trans hQK)]
    refine sup_le ?_ ?_
    · intro x hx
      refine Subgroup.mem_comap.2 (le_normalizer ?_)
      exact Subgroup.mem_map.2 ⟨x, hX₂M hx, rfl⟩
    · intro x hx
      refine Subgroup.mem_comap.2 (mem_normalizer_fintype fun y hy => ?_)
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_map.2 ⟨x * n * x⁻¹, ?_, by simp⟩
      exact hFnorm x hx n hn
  have hT : IsPGroup 2 ↥(Qπ ⊔ Mπ) := IsPGroup.to_sup_of_normal_right' hQπp hMπp hQN
  have hQ₀le : Q₀ ≤ Qπ := by
    intro q hq
    have hq' : Data.theta h hf q ∈ d.X₂ ⊔ d.F := hq
    refine Subgroup.mem_map.2 ⟨⟨Data.theta h hf q, Data.theta_mem_sup h hf q⟩, hq', ?_⟩
    exact Data.proj0_theta h hf q
  have hQ₀card : 2 ^ 6 ≤ Nat.card ↥Q₀ := by
    have hle : d.X₂ ⊔ d.F ≤ (Data.theta h hf).range := by
      rw [Data.range_theta h hKU hf]
      exact d.X₂_sup_F_le_K₃
    have hmap : Q₀.map (Data.theta h hf) = d.X₂ ⊔ d.F := Subgroup.map_comap_eq_self hle
    calc 2 ^ 6 ≤ Nat.card ↥(d.X₂ ⊔ d.F) := d.card_X₂_sup_F
      _ = Nat.card ↥(Q₀.map (Data.theta h hf)) := by rw [hmap]
      _ = Nat.card ↥Q₀ := Subgroup.card_map_of_injective (Data.theta_injective h hf)
  have hEq : Q₀ = Qπ ⊔ Mπ :=
    eq_of_le_of_isPGroup_of_card (hQ₀le.trans le_sup_left) hT hQ₀card
      (Data.card_K₀_dvd h hKU hf)
  have hm' : m ∈ M := hm
  have hmK : m ∈ K' := hMK hm'
  have hπm : π ⟨m, hmK⟩ = ⟨a, ha⟩ := by
    refine Subtype.ext ?_
    have : (⟨m, hmK⟩ : ↥K') = ⟨a * b, mul_mem (mem_sup_left ha) (mem_sup_right hb)⟩ :=
      Subtype.ext hmab
    rw [this]
    exact Data.proj0_mul hf ha hb
  have hmem : (⟨a, ha⟩ : ↥K₀) ∈ Q₀ := by
    rw [hEq]
    refine mem_sup_right ?_
    rw [← hπm]
    exact Subgroup.mem_map.2 ⟨⟨m, hmK⟩, hm', rfl⟩
  have := (Subgroup.mem_comap.1 hmem)
  rwa [Data.theta_apply] at this

end Comp

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
