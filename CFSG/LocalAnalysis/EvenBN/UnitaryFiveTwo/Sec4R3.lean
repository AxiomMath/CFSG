module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4R2Two
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSTwo

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

theorem exists_mem_normalizer_not_mem_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H < K) :
    ∃ x ∈ K, x ∈ normalizer (H : Set G) ∧ x ∉ H := by
  have := hK.isNilpotent
  have hnc := Group.normalizerCondition_of_isNilpotent (G := K)
  have hlt : H.subgroupOf K < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hHK.ne (le_antisymm hHK.le fun x hx => ?_)
    have : (⟨x, hx⟩ : K) ∈ H.subgroupOf K := htop ▸ mem_top _
    exact this
  obtain ⟨x, hxN, hxH⟩ := IsConcreteLE.exists_of_lt (hnc _ hlt)
  refine ⟨x, x.2, mem_normalizer_fintype fun y hy => ?_, hxH⟩
  have := (mem_normalizer_iff.1 hxN ⟨y, hHK.le hy⟩).1 hy
  exact this

theorem mem_X₃sub_sup_X₄sub_of_mem_A₁sub {a : SU52} (ha : a ∈ A₁sub) (h10 : mat a 1 0 = 0) :
    a ∈ X₃sub ⊔ X₄sub := by
  obtain ⟨a₂, a₃, a₄, b₄, hv, e⟩ := exists_nf_of_mem_A₁sub ha
  have hc := cvec_nf a₂ a₃ a₄ b₄
  rw [← e] at hc
  have h2 : a₂ = 0 := by simpa [cvec, ι3, h10] using (congrFun hc 0).symm
  subst h2
  have hv' : a₄ * bar a₄ = b₄ + bar b₄ := hv
  have ea : a = x₃SU a₃ * x₄SU a₄ b₄ hv' := ext_mat (by
    rw [e, x₂Mat_zero, Matrix.one_mul, mat_mul, mat_x₃SU, mat_x₄SU])
  rw [ea]
  exact mul_mem (mem_sup_left (x₃SU_mem a₃)) (mem_sup_right (x₄SU_mem _ _ _))

theorem mem_Z₂sub_of_mat {a : SU52} (ha : a ∈ A₁sub) (h10 : mat a 1 0 = 0)
    (h20 : mat a 2 0 = 0) : a ∈ Z₂sub := by
  obtain ⟨a₂, a₃, a₄, b₄, hv, e⟩ := exists_nf_of_mem_A₁sub ha
  have hc := cvec_nf a₂ a₃ a₄ b₄
  rw [← e] at hc
  have h2 : a₂ = 0 := by simpa [cvec, ι3, h10] using (congrFun hc 0).symm
  have h4 : a₄ = 0 := by simpa [cvec, ι3, h20] using (congrFun hc 1).symm
  subst h2 h4
  have hv' : (0 : F4) * bar 0 = b₄ + bar b₄ := hv
  have ea : a = x₃SU a₃ * x₄SU 0 b₄ hv' := ext_mat (by
    rw [e, x₂Mat_zero, Matrix.one_mul, mat_mul, mat_x₃SU, mat_x₄SU])
  rw [ea]
  exact mul_mem (mem_sup_left (x₃SU_mem a₃))
    (mem_sup_right (mem_x₄Sub.2 ⟨0, b₄, rfl, mat_x₄SU _ _ _⟩))

theorem inv_mul_mem_Z₂sub {a a' : SU52} (ha : a ∈ A₁sub) (ha' : a' ∈ A₁sub)
    (h10 : mat a 1 0 = mat a' 1 0) (h20 : mat a 2 0 = mat a' 2 0) : a⁻¹ * a' ∈ Z₂sub := by
  have hinv : cvec (mat a⁻¹) + cvec (mat a) = 0 := by
    rw [← cvec_mul (inv_mem ha) ha, inv_mul_cancel, mat_one, cvec_one]
  have hc := cvec_mul (inv_mem ha) ha'
  have i0 : mat a⁻¹ 1 0 + mat a 1 0 = 0 := congrFun hinv 0
  have i1 : mat a⁻¹ 2 0 + mat a 2 0 = 0 := congrFun hinv 1
  have c0 : mat (a⁻¹ * a') 1 0 = mat a⁻¹ 1 0 + mat a' 1 0 := congrFun hc 0
  have c1 : mat (a⁻¹ * a') 2 0 = mat a⁻¹ 2 0 + mat a' 2 0 := congrFun hc 1
  refine mem_Z₂sub_of_mat (mul_mem (inv_mem ha) ha') ?_ ?_
  · rw [c0]
    linear_combination i0 - h10
  · rw [c1]
    linear_combination i1 - h20

theorem mat_one_zero_of_mem_X₃sub_sup_X₄sub {a : SU52} (ha : a ∈ X₃sub ⊔ X₄sub) :
    mat a 1 0 = 0 :=
  (mem_X₄sub_sup_Fsub_iff_mat.1 ((sup_le ((le_sup_right.trans le_sup_left : X₃sub ≤ Fsub).trans
    le_sup_right) le_sup_left : X₃sub ⊔ X₄sub ≤ X₄sub ⊔ Fsub) ha)).2.2

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

omit [Finite G] in
theorem X₃₄_le_A₁ : d.X₃ ⊔ d.X₄ ≤ d.A₁ :=
  sup_le (d.pull_mono X₃sub_le_A₁sub) (d.pull_mono X₄sub_le_A₁sub')

omit [Finite G] in
theorem X₃₄_le_L : d.X₃ ⊔ d.X₄ ≤ d.L := sup_le (d.pull_le_L _) (d.pull_le_L _)

omit [Finite G] in
theorem X₃₄_le_XF : d.X₃ ⊔ d.X₄ ≤ d.X₄ ⊔ d.F :=
  sup_le ((d.pull_mono (le_sup_right.trans le_sup_left : X₃sub ≤ Fsub)).trans le_sup_right)
    le_sup_left

theorem X₃₄_comm_W
    (h : d.Hyp) {a w : G}
    (ha : a ∈ d.X₃ ⊔ d.X₄) (hw : w ∈ d.W) : a * w = w * a :=
  h.A₁_comm_W (X₃₄_le_A₁ ha) hw

theorem ι_mem_normalizer_pull {n : SU52} {M : Subgroup SU52}
    (hn : n ∈ normalizer (M : Set SU52)) : d.ι n ∈ normalizer (d.pull M : Set G) :=
  mem_normalizer_fintype fun x hx => by
    obtain ⟨m, hm, rfl⟩ := hx
    rw [ι_conj]
    exact ⟨_, (mem_normalizer_iff.1 hn m).1 hm, rfl⟩

theorem e₂_mem_NHS (h : d.Hyp) : d.e₂ ∈ normalizer (d.S : Set G) ⊓ d.H :=
  Subgroup.mem_inf.2 ⟨ι_mem_normalizer_pull e₂SU_mem_normalizer_Ssub, h.L_le_H (d.ι_mem _)⟩

omit [Finite G] in
theorem mem_ZX₄_of_central_S {a : G} (ha : a ∈ d.S) (hc : ∀ b ∈ d.S, a * b = b * a) :
    a ∈ d.ZX₄ := by
  obtain ⟨α, hα, rfl⟩ := ha
  refine ⟨α, ?_, rfl⟩
  rw [← Ssub_inf_centralizer_Ssub]
  exact Subgroup.mem_inf.2 ⟨hα, mem_centralizer_iff.2 fun β hβ => d.ι_injective (by
    rw [map_mul, map_mul]
    exact (hc _ ⟨β, hβ, rfl⟩).symm)⟩

omit [Finite G] in
theorem comm_z_of_mem_normalizer_S {g : G} (hg : g ∈ normalizer (d.S : Set G)) :
    g * d.z = d.z * g := by
  have hm : g * d.z * g⁻¹ ∈ d.S :=
    (mem_normalizer_iff.1 hg _).1 (d.A₁_le_S (ZX₄_le_A₁ z_mem_ZX₄))
  have hcen : ∀ b ∈ d.S, g * d.z * g⁻¹ * b = b * (g * d.z * g⁻¹) := by
    have := conj_central_of_mem_normalizer (inv_mem hg) fun b hb =>
      (ZX₄_comm_S z_mem_ZX₄ hb).symm
    simpa using this
  rcases eq_one_or_eq_z (mem_ZX₄_of_central_S hm hcen) with e | e
  · exfalso
    apply z_ne_one (d := d)
    calc d.z = g⁻¹ * (g * d.z * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · calc g * d.z = g * d.z * g⁻¹ * g := by group
      _ = d.z * g := by rw [e]

theorem NHS_le_normalizer_W
    (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.W : Set G) := fun g hg => by
  have hgY := h.NHS_le_normalizer_Y hg
  have hgS := (Subgroup.mem_inf.1 hg).1
  refine mem_normalizer_fintype fun w hw => ?_
  obtain ⟨hwY, hwC⟩ := Subgroup.mem_inf.1 hw
  refine Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hgY w).1 hwY,
    mem_centralizer_iff.2 fun s hs => ?_⟩
  have hs' : g⁻¹ * s * g ∈ d.S := by
    have := (mem_normalizer_iff.1 (inv_mem hgS) s).1 hs
    rwa [inv_inv] at this
  have e := mem_centralizer_iff.1 hwC _ hs'
  calc s * (g * w * g⁻¹) = g * ((g⁻¹ * s * g) * w) * g⁻¹ := by group
    _ = g * (w * (g⁻¹ * s * g)) * g⁻¹ := by rw [e]
    _ = g * w * g⁻¹ * s := by group

theorem NHS_le_normalizer_V₂
    (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.V₂ : Set G) := fun g hg => by
  have hgY := h.NHS_le_normalizer_Y hg
  have hgW := h.NHS_le_normalizer_W hg
  have hgS := (Subgroup.mem_inf.1 hg).1
  refine mem_normalizer_fintype fun v hv => ?_
  obtain ⟨hvY, hvW⟩ := (h.mem_V₂_iff).1 hv
  refine (h.mem_V₂_iff).2 ⟨(mem_normalizer_iff.1 hgY v).1 hvY, fun s hs => ?_⟩
  have hs' : g⁻¹ * s * g ∈ d.S := by
    have := (mem_normalizer_iff.1 (inv_mem hgS) s).1 hs
    rwa [inv_inv] at this
  have e := (mem_normalizer_iff.1 hgW _).1 (hvW _ hs')
  rwa [show g * ((g⁻¹ * s * g) * v * (g⁻¹ * s * g)⁻¹ * v⁻¹) * g⁻¹ =
    s * (g * v * g⁻¹) * s⁻¹ * (g * v * g⁻¹)⁻¹ by group] at e

theorem NHS_le_normalizer_R₂
    (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ normalizer (d.R₂ : Set G) := fun g hg => by
  obtain ⟨hgS, hgH⟩ := Subgroup.mem_inf.1 hg
  refine mem_normalizer_sup ?_ (h.NHS_le_normalizer_V₂ hg)
  refine mem_normalizer_sup hgS (mem_normalizer_fintype fun x hx => ?_)
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hx
  rw [(Commute.zpow_right (mem_centralizer_singleton_iff.1 hgH) n).eq, mul_inv_cancel_right]
  exact zpow_mem (mem_zpowers _) n

theorem R_comm_z (h : d.Hyp) {r : G} (hr : r ∈ d.R) : r * d.z = d.z * r := by
  have hle : d.R ≤ centralizer ({d.z} : Set G) := sup_le
    (fun s hs => mem_centralizer_singleton_iff.2 (ZX₄_comm_S z_mem_ZX₄ hs))
    (zpowers_le.2 (mem_centralizer_singleton_iff.2
      (comm_of_mem_centralizer h.t_mem (d.ι_mem zSU)).symm))
  exact mem_centralizer_singleton_iff.1 (hle hr)

theorem AW_le_D₃
    (h : d.Hyp) :
    d.AW ≤ d.D₃ := fun _ hx => Subgroup.mem_inf.2 ⟨(d.R₂).le_normalizer
  ((sup_le (fun _ ha => mem_sup_left (mem_sup_left (d.A₁_le_S ha)))
    (h.W_le_V₂.trans le_sup_right) : d.AW ≤ d.R₂) hx), h.AW_le_D₁ hx⟩

theorem A₁_le_normalizer_V₂
    (h : d.Hyp) :
    d.A₁ ≤ normalizer (d.V₂ : Set G) := fun a ha => mem_normalizer_fintype fun v hv => by
  have hw := ((h.mem_V₂_iff).1 hv).2 a (d.A₁_le_S ha)
  rw [show a * v * a⁻¹ = (a * v * a⁻¹ * v⁻¹) * v by group]
  exact mul_mem (h.W_le_V₂ hw) hv

theorem crossed_set_mul_mem
    (h : d.Hyp)
    {D : Subgroup G} (hD : D ≤ d.D₁) {α β : SU52} (hα : α ∈ A₁sub) (hβ : β ∈ A₁sub)
    (h₁ : ∃ u ∈ D, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = d.ι α * w)
    (h₂ : ∃ u ∈ D, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = d.ι β * w) :
    ∃ u ∈ D, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = d.ι (α * β) * w := by
  obtain ⟨u₁, hu₁, w₁, hw₁, e1⟩ := h₁
  obtain ⟨u₂, hu₂, w₂, hw₂, e2⟩ := h₂
  have hu₂U := (Subgroup.mem_inf.1 (hD hu₂)).1
  have hu₂N := (Subgroup.mem_inf.1 (mem_UA₁_iff.1 hu₂U).1).2
  obtain ⟨c, hc, hce⟩ : ∃ c ∈ d.W, u₂ * d.ι α * u₂⁻¹ = d.ι α * c :=
    ⟨_, (h.mem_W_of_mem_UA₁_of_mem_AW hu₂U
      (mem_sup_left (⟨α, hα, rfl⟩ : d.ι α ∈ d.A₁))).1, by group⟩
  obtain ⟨w₃, hw₃, hw₃e⟩ : ∃ w₃ ∈ d.W, u₂ * w₁ * u₂⁻¹ = w₃ :=
    ⟨_, (mem_normalizer_iff.1 hu₂N w₁).1 hw₁, rfl⟩
  have e1' : u₁ * d.t * u₁⁻¹ = d.ι α * w₁ * d.t := by
    rw [← e1, mul_assoc _ d.t d.t, h.t_mul_t, mul_one]
  have hcomm : d.ι β * (c * w₃) = (c * w₃) * d.ι β :=
    h.A₁_comm_W ⟨β, hβ, rfl⟩ (mul_mem hc hw₃)
  refine ⟨u₂ * u₁, mul_mem hu₂ hu₁, c * w₃ * w₂, mul_mem (mul_mem hc hw₃) hw₂, ?_⟩
  calc u₂ * u₁ * d.t * (u₂ * u₁)⁻¹ * d.t = u₂ * (u₁ * d.t * u₁⁻¹) * u₂⁻¹ * d.t := by group
    _ = u₂ * (d.ι α * w₁ * d.t) * u₂⁻¹ * d.t := by rw [e1']
    _ = (u₂ * d.ι α * u₂⁻¹) * (u₂ * w₁ * u₂⁻¹) * (u₂ * d.t * u₂⁻¹ * d.t) := by group
    _ = d.ι α * (c * w₃ * d.ι β) * w₂ := by rw [hce, hw₃e, e2]; group
    _ = d.ι α * (d.ι β * (c * w₃)) * w₂ := by rw [← hcomm]
    _ = d.ι (α * β) * (c * w₃ * w₂) := by rw [map_mul]; group

end Data.Hyp

section C7

namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem NHS_le_XW
    (h : d.Hyp) :
    normalizer (d.S : Set G) ⊓ d.H ≤ d.XW := fun _ hg =>
  h.mem_XW_of_comm_z_of_mem_H (Subgroup.mem_inf.1 hg).2
    (comm_z_of_mem_normalizer_S (Subgroup.mem_inf.1 hg).1)

theorem conj_mem_D₃
    (h : d.Hyp) {g u : G}
    (hg : g ∈ normalizer (d.S : Set G) ⊓ d.H) (hu : u ∈ d.D₃) : g * u * g⁻¹ ∈ d.D₃ := by
  have hgR := h.NHS_le_normalizer_R₂ hg
  exact Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgR (Subgroup.mem_inf.1 hu).1) (inv_mem hgR),
    h.conj_mem_D₁ (h.NHS_le_XW hg) (Subgroup.mem_inf.1 hu).2⟩

theorem R_le_XW
    (h : d.Hyp) :
    d.R ≤ d.XW := fun _ hr => h.mem_XW_of_comm_z_of_mem_H (h.R_le_H hr) (h.R_comm_z hr)

theorem R_le_normalizer_D₁
    (h : d.Hyp) :
    d.R ≤ normalizer (d.D₁ : Set G) := fun _ hr =>
  mem_normalizer_fintype fun _ hu => h.conj_mem_D₁ (h.R_le_XW hr) hu

theorem card_D₁_sup_R
    (h : d.Hyp) :
    Nat.card (d.D₁ ⊔ d.R : Subgroup G) = 2 ^ 18 := by
  have hinf : d.D₁ ⊓ d.R = d.A₁ := by
    refine le_antisymm (fun x hx => ?_) (le_inf h.A₁_le_D₁ fun a ha => mem_sup_left
      (d.A₁_le_S ha))
    rw [← h.D₁_inf_H]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, h.R_le_H (Subgroup.mem_inf.1 hx).2⟩
  have e := card_sup_mul_card_inf_of_le_normalizer d.D₁ d.R h.R_le_normalizer_D₁
  rw [hinf, h.card_D₁, h.card_R, d.card_A₁] at e
  norm_num at e ⊢
  omega

theorem exists_mem_D₃_not_mem
    (h : d.Hyp) :
    ∃ u ∈ d.D₃, u ∉ d.A₁ ⊔ d.V₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (d.D₁ ⊔ d.R : Subgroup G) := IsPGroup.of_card h.card_D₁_sup_R
  have hle : d.R₂ ≤ d.D₁ ⊔ d.R := sup_le le_sup_right (h.V₂_le_D₁.trans le_sup_left)
  have hlt : d.R₂ < d.D₁ ⊔ d.R := lt_of_le_of_ne hle fun e => by
    have := congrArg (fun K : Subgroup G => Nat.card K) e
    simp only [h.card_R₂, h.card_D₁_sup_R] at this
    norm_num at this
  obtain ⟨x, hxK, hxN, hxR⟩ := exists_mem_normalizer_not_mem_of_lt hP hlt
  have hset := coe_mul_of_right_le_normalizer_left d.D₁ d.R h.R_le_normalizer_D₁
  have hmem : x ∈ (d.D₁ : Set G) * (d.R : Set G) := by
    rw [← hset]
    exact hxK
  obtain ⟨u, hu, r, hr, rfl⟩ := Set.mem_mul.1 hmem
  have hrN : r ∈ normalizer (d.R₂ : Set G) := (d.R₂).le_normalizer (mem_sup_left hr)
  refine ⟨u, Subgroup.mem_inf.2 ⟨?_, hu⟩, fun huA => hxR ?_⟩
  · have := mul_mem hxN (inv_mem hrN)
    rwa [mul_inv_cancel_right] at this
  · exact mul_mem ((sup_le (fun a ha => mem_sup_left (mem_sup_left (d.A₁_le_S ha)))
      le_sup_right : d.A₁ ⊔ d.V₂ ≤ d.R₂) huA) (mem_sup_left hr)

theorem V₂_le_D₃
    (h : d.Hyp) :
    d.V₂ ≤ d.D₃ := fun _ hv =>
  Subgroup.mem_inf.2 ⟨(d.R₂).le_normalizer (mem_sup_right hv), h.V₂_le_D₁ hv⟩

theorem crossed_mem_of_mem_D₃
    (h : d.Hyp) {u : G}
    (hu : u ∈ d.D₃) : u * d.t * u⁻¹ * d.t ∈ (d.X₃ ⊔ d.X₄) ⊔ d.W := by
  obtain ⟨huN, huD⟩ := Subgroup.mem_inf.1 hu
  have h1 := h.crossed_mem_of_mem_normalizer_R₂ huN
  obtain ⟨a, ha, w, hw, e⟩ := h.exists_eq_mul_of_mem_AW (h.conj_t_mul_t_mem_AW (D₁_le_XW huD))
  have haX : a ∈ (d.X₄ ⊔ d.F) ⊔ d.V₂ := by
    rw [show a = (u * d.t * u⁻¹ * d.t) * w⁻¹ by rw [← e]; group]
    exact mul_mem h1 (mem_sup_right (inv_mem (h.W_le_V₂ hw)))
  obtain ⟨k, hk, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun k hk v hv => (h.Y_comm_XFW (h.V₂_le_Y hv) (mem_sup_left hk)).symm) haX
  have hvH : v ∈ d.H := by
    have := mul_mem (inv_mem (h.L_le_H (d.pull_le_L _ (XF_le_S hk))))
      (h.L_le_H (d.pull_le_L _ ha))
    rwa [inv_mul_cancel_left] at this
  have hvZ : v ∈ d.Z₂ := by
    rw [← h.V₂_inf_H]
    exact Subgroup.mem_inf.2 ⟨hv, hvH⟩
  have hkv : k * v ∈ d.X₄ ⊔ d.F := mul_mem hk (mem_sup_right (Z₂_le_F hvZ))
  obtain ⟨α, hα, hαe⟩ := ha
  have hαX : α ∈ X₄sub ⊔ Fsub := by
    have : d.ι α ∈ d.pull (X₄sub ⊔ Fsub) := by
      rw [d.pull_sup, hαe]
      exact hkv
    exact d.ι_mem_pull_iff.1 this
  have hα34 := mem_X₃sub_sup_X₄sub_of_mem_A₁sub hα (mem_X₄sub_sup_Fsub_iff_mat.1 hαX).2.2
  rw [← e, ← hαe]
  refine mul_mem (mem_sup_left ?_) (mem_sup_right hw)
  have : d.ι α ∈ d.pull (X₃sub ⊔ X₄sub) := ⟨α, hα34, rfl⟩
  rw [d.pull_sup] at this
  exact this

theorem exists_D₃_conj_t
    (h : d.Hyp) {a : G}
    (ha : a ∈ d.X₃ ⊔ d.X₄) : ∃ u ∈ d.D₃, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = a * w := by
  let T : Set SU52 :=
    {α | α ∈ A₁sub ∧ ∃ u ∈ d.D₃, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = d.ι α * w}
  have hD : d.D₃ ≤ d.D₁ := fun _ hu => (Subgroup.mem_inf.1 hu).2
  have h1 : (1 : SU52) ∈ T := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by simp [h.t_mul_t]⟩
  have hmul : ∀ α ∈ T, ∀ β ∈ T, α * β ∈ T := fun α hα β hβ =>
    ⟨mul_mem hα.1 hβ.1, h.crossed_set_mul_mem hD hα.1 hβ.1 hα.2 hβ.2⟩
  have hZ : ∀ γ ∈ Z₂sub, γ ∈ T := fun γ hγ => by
    refine ⟨Z₂sub_le_A₁sub hγ, ?_⟩
    obtain ⟨v, hv, hvt⟩ := h.exists_V₂_crossed_eq (⟨γ, hγ, rfl⟩ : d.ι γ ∈ d.Z₂)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.Y_sq (h.V₂_le_Y hv))
    refine ⟨v, h.V₂_le_D₃ hv, 1, one_mem _, ?_⟩
    rw [mul_one, ← hvt, hvi]
  have h34 : ∀ α ∈ T, α ∈ X₃sub ⊔ X₄sub := fun α ⟨_, u, hu, w, hw, e⟩ => by
    have hθ := h.crossed_mem_of_mem_D₃ hu
    rw [e] at hθ
    have hι : d.ι α ∈ (d.X₃ ⊔ d.X₄) ⊔ d.W := by
      have := mul_mem hθ (mem_sup_right (inv_mem hw))
      rwa [mul_inv_cancel_right] at this
    obtain ⟨k, hk, w', hw', e'⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun k hk w hw => h.X₃₄_comm_W hk hw) hι
    have hw'Z : w' ∈ d.ZX₄ := by
      rw [← h.W_inf_H]
      refine Subgroup.mem_inf.2 ⟨hw', h.L_le_H ?_⟩
      rw [show w' = k⁻¹ * d.ι α by rw [← e']; group]
      exact mul_mem (inv_mem (X₃₄_le_L hk)) (d.ι_mem α)
    have : d.ι α ∈ d.pull (X₃sub ⊔ X₄sub) := by
      rw [d.pull_sup, ← e']
      exact mul_mem hk (mem_sup_right (d.pull_mono ZX₄sub_le_X₄sub hw'Z))
    exact d.ι_mem_pull_iff.1 this
  have he : ∀ α ∈ T, e₂SU * α * e₂SU⁻¹ ∈ T := fun α ⟨hα, u, hu, w, hw, e⟩ => by
    have heX := h.NHS_le_XW h.e₂_mem_NHS
    refine ⟨conj_mem_A₁sub_of_comm_z (comm_of_mem_CzSub e₂SU_mem_CzSub) hα,
      d.e₂ * u * d.e₂⁻¹, h.conj_mem_D₃ h.e₂_mem_NHS hu, d.e₂ * w * d.e₂⁻¹,
      (mem_normalizer_iff.1 (Subgroup.mem_inf.1 heX).2 w).1 hw, ?_⟩
    rw [crossed_conj_of_mem_H (Subgroup.mem_inf.1 h.e₂_mem_NHS).2, e, ← ι_conj]
    simp only [Data.e₂]
    group
  obtain ⟨α₀, hα₀T, hα₀⟩ : ∃ α ∈ T, mat α 2 0 ≠ 0 := by
    obtain ⟨u, hu, hu'⟩ := h.exists_mem_D₃_not_mem
    obtain ⟨a, ⟨α, hα, rfl⟩, w, hw, e⟩ :=
      h.exists_eq_mul_of_mem_AW (h.conj_t_mul_t_mem_AW (D₁_le_XW (hD hu)))
    have hαT : α ∈ T := ⟨hα, u, hu, w, hw, e.symm⟩
    refine ⟨α, hαT, fun h20 => hu' (h.mem_A₁V₂_of_crossed_mem (hD hu) ?_)⟩
    have hαZ := mem_Z₂sub_of_mat hα (mat_one_zero_of_mem_X₃sub_sup_X₄sub (h34 α hαT)) h20
    rw [← e]
    exact mul_mem (mem_sup_left ⟨α, hαZ, rfl⟩) (mem_sup_right hw)
  have hall : ∀ b : F4, ∃ α ∈ T, mat α 2 0 = b := by
    have hadd : ∀ α ∈ T, ∀ β ∈ T, mat (α * β) 2 0 = mat α 2 0 + mat β 2 0 :=
      fun α hα β hβ => congrFun (cvec_mul hα.1 hβ.1) 1
    have hβ₁ := he α₀ hα₀T
    have e1 := mat_conj_e₂_two_zero α₀
    intro b
    have hb : b = b * (mat α₀ 2 0)⁻¹ * mat α₀ 2 0 := (inv_mul_cancel_right₀ hα₀ b).symm
    rcases F4_cases (b * (mat α₀ 2 0)⁻¹) with hc | hc | hc | hc
    · refine ⟨1, h1, ?_⟩
      rw [hb, hc, zero_mul, mat_one, Matrix.one_apply_ne (by decide)]
    · exact ⟨α₀, hα₀T, by rw [hb, hc, one_mul]⟩
    · exact ⟨_, hβ₁, by rw [e1, hb, hc]⟩
    · refine ⟨α₀ * (e₂SU * α₀ * e₂SU⁻¹), hmul _ hα₀T _ hβ₁, ?_⟩
      rw [hadd _ hα₀T _ hβ₁, e1, hb, hc]
      ring
  obtain ⟨β, hβ, rfl⟩ : a ∈ d.pull (X₃sub ⊔ X₄sub) := by
    rw [d.pull_sup]
    exact ha
  have hβA : β ∈ A₁sub := (sup_le X₃sub_le_A₁sub X₄sub_le_A₁sub') hβ
  obtain ⟨α, hαT, hαb⟩ := hall (mat β 2 0)
  have hγ := inv_mul_mem_Z₂sub hαT.1 hβA (by
    rw [mat_one_zero_of_mem_X₃sub_sup_X₄sub (h34 α hαT),
      mat_one_zero_of_mem_X₃sub_sup_X₄sub hβ]) hαb
  obtain ⟨-, hT⟩ := hmul α hαT _ (hZ _ hγ)
  rw [mul_inv_cancel_left] at hT
  exact hT

theorem mem_D₃_of_crossed_mem
    (h : d.Hyp) {x : G}
    (hx : x ∈ d.D₁) (hθ : x * d.t * x⁻¹ * d.t ∈ (d.X₃ ⊔ d.X₄) ⊔ d.W) : x ∈ d.D₃ := by
  have hD : d.D₃ ≤ d.D₁ := fun _ hu => (Subgroup.mem_inf.1 hu).2
  obtain ⟨a, ha, w₁, hw₁, e1⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha w hw => h.X₃₄_comm_W ha hw) hθ
  obtain ⟨u, hu, w₂, hw₂, e2⟩ := h.exists_D₃_conj_t (inv_mem ha)
  obtain ⟨w, hw, e⟩ := h.crossed_mul_mem (Subgroup.mem_inf.1 (hD hu)).1 (D₁_le_XW hx)
  have hux : u * x * d.t * (u * x)⁻¹ * d.t ∈ d.W := by
    rw [e, ← e1, e2, show a * w₁ * (a⁻¹ * w₂) * w = a * w₁ * a⁻¹ * w₂ * w by group,
      h.X₃₄_comm_W ha hw₁, mul_inv_cancel_right]
    exact mul_mem (mul_mem hw₁ hw₂) hw
  have := mul_mem (inv_mem hu)
    (h.AW_le_D₃ ((h.crossed_mem_W_iff_of_mem_D₁ (mul_mem (hD hu) hx)).1 hux))
  rwa [inv_mul_cancel_left] at this

theorem card_D₃
    (h : d.Hyp) :
    Nat.card d.D₃ = 2 ^ 12 := by
  have hD : d.D₃ ≤ d.D₁ := fun _ hu => (Subgroup.mem_inf.1 hu).2
  let φ : d.D₃ →* Equiv.Perm d.OmW :=
    d.omegaPermW.comp (Subgroup.inclusion (hD.trans D₁_le_XW))
  let : MulAction d.D₃ d.OmW := MulAction.compHom _ φ
  have hsmul : ∀ (u : d.D₃) (S : d.OmW),
      ((u • S : d.OmW) : Set G) = (fun g => (u : G) * g * (u : G)⁻¹) '' (S : Set G) := by
    intro u S
    rw [MulAction.compHom_smul_def, Equiv.Perm.smul_def, MonoidHom.comp_apply,
      Data.omegaPermW_apply, Subgroup.coe_inclusion]
  have hstab : MulAction.stabilizer d.D₃ (⟨_, tW_mem_OmW⟩ : d.OmW) = d.AW.subgroupOf d.D₃ := by
    ext u
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf, ← h.crossed_mem_W_iff_of_mem_D₁ (hD u.2),
      Subtype.ext_iff, hsmul]
    rw [conj_image_smul_coset (Subgroup.mem_inf.1 (D₁_le_XW (hD u.2))).2, leftCoset_eq_iff,
      show ((u : G) * d.t * (u : G)⁻¹)⁻¹ * d.t = (u : G) * d.t * (u : G)⁻¹ * d.t by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, h.t_inv]
        group]
  let f : (Fin 2 → F4) → d.OmW := fun c =>
    ⟨(d.ι (nfA₁ ![0, c 0, c 1]) * d.t) • (d.W : Set G),
      (h.mem_OmW_iff_of_elem).2 ⟨_, ⟨_, nfA₁_mem _, rfl⟩, rfl⟩⟩
  have hf : Function.Injective f := fun c c' e => by
    have := (h.coset_ι_eq_iff (nfA₁_mem _) (nfA₁_mem _)).1 (congrArg Subtype.val e)
    rw [cvec_nfA₁, cvec_nfA₁] at this
    funext i
    fin_cases i
    · exact congrFun this 1
    · exact congrFun this 2
  have horb : MulAction.orbit d.D₃ (⟨_, tW_mem_OmW⟩ : d.OmW) = Set.range f := by
    ext S
    constructor
    · rintro ⟨u, rfl⟩
      obtain ⟨k, hk, w, hw, e⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
        (fun k hk w hw => h.X₃₄_comm_W hk hw) (h.crossed_mem_of_mem_D₃ u.2)
      obtain ⟨β, hβ, rfl⟩ : k ∈ d.pull (X₃sub ⊔ X₄sub) := by
        rw [d.pull_sup]
        exact hk
      have hβA : β ∈ A₁sub := (sup_le X₃sub_le_A₁sub X₄sub_le_A₁sub') hβ
      refine ⟨![mat β 2 0, mat β 3 0], Subtype.ext ?_⟩
      rw [hsmul]
      change (d.ι (nfA₁ ![0, mat β 2 0, mat β 3 0]) * d.t) • (d.W : Set G) =
        (fun g => (u : G) * g * (u : G)⁻¹) '' (d.t • (d.W : Set G))
      rw [conj_image_smul_coset (Subgroup.mem_inf.1 (D₁_le_XW (hD u.2))).2,
        show (u : G) * d.t * (u : G)⁻¹ = d.ι β * w * d.t by
          rw [e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one],
        h.smul_coset_mul_t hw]
      refine (h.coset_ι_eq_iff (nfA₁_mem _) hβA).2 ?_
      rw [cvec_nfA₁]
      funext i
      fin_cases i
      · exact (mat_one_zero_of_mem_X₃sub_sup_X₄sub hβ).symm
      · rfl
      · rfl
    · rintro ⟨c, rfl⟩
      have hm : d.ι (nfA₁ ![0, c 0, c 1]) ∈ d.X₃ ⊔ d.X₄ := by
        have : d.ι (nfA₁ ![0, c 0, c 1]) ∈ d.pull (X₃sub ⊔ X₄sub) :=
          ⟨_, mem_X₃sub_sup_X₄sub_of_mem_A₁sub (nfA₁_mem _)
            (congrFun (cvec_nfA₁ ![0, c 0, c 1]) 0), rfl⟩
        rw [d.pull_sup] at this
        exact this
      obtain ⟨u, hu, w, hw, e⟩ := h.exists_D₃_conj_t hm
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      rw [hsmul]
      change (fun g => u * g * u⁻¹) '' (d.t • (d.W : Set G)) =
        (d.ι (nfA₁ ![0, c 0, c 1]) * d.t) • (d.W : Set G)
      rw [conj_image_smul_coset (Subgroup.mem_inf.1 (D₁_le_XW (hD hu))).2,
        show u * d.t * u⁻¹ = d.ι (nfA₁ ![0, c 0, c 1]) * w * d.t by
          rw [← e, mul_assoc _ d.t d.t, h.t_mul_t, mul_one],
        h.smul_coset_mul_t hw]
  have hidx := MulAction.index_stabilizer (G := d.D₃) (⟨_, tW_mem_OmW⟩ : d.OmW)
  rw [horb, Set.ncard_range_of_injective hf, hstab] at hidx
  rw [← (d.AW.subgroupOf d.D₃).card_mul_index, hidx,
    Nat.card_congr (subgroupOfEquivOfLe h.AW_le_D₃).toEquiv, h.card_AW, Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_fin, F4.card]
  norm_num

theorem crossed_mem_Z₂_of_mem_A₁V₂
    (h : d.Hyp) {x : G} (hx : x ∈ d.A₁ ⊔ d.V₂) :
    x * d.t * x⁻¹ * d.t ∈ d.Z₂ := by
  have hset := coe_mul_of_left_le_normalizer_right d.A₁ d.V₂ h.A₁_le_normalizer_V₂
  have hmem : x ∈ (d.A₁ : Set G) * (d.V₂ : Set G) := by
    rw [← hset]
    exact hx
  obtain ⟨a, ha, v, hv, rfl⟩ := Set.mem_mul.1 hmem
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (h.Y_sq (h.V₂_le_Y hv))
  have hθ : v * d.t * v⁻¹ * d.t ∈ d.Z₂ := by
    have := h.crossed_mem_Z₂_of_mem_V₂ hv
    rw [hvi] at this ⊢
    exact this
  have hat : a⁻¹ * d.t = d.t * a⁻¹ := h.t_comm_of_mem_L (d.pull_le_L _ (inv_mem ha))
  rw [show a * v * d.t * (a * v)⁻¹ * d.t = a * (v * d.t * v⁻¹) * (a⁻¹ * d.t) by group, hat,
    show a * (v * d.t * v⁻¹) * (d.t * a⁻¹) = a * (v * d.t * v⁻¹ * d.t) * a⁻¹ by group]
  have hc := Z₂_comm_S hθ (d.A₁_le_S ha)
  rw [show a * (v * d.t * v⁻¹ * d.t) * a⁻¹ = (a * (v * d.t * v⁻¹ * d.t) * a⁻¹ *
    (v * d.t * v⁻¹ * d.t)⁻¹) * (v * d.t * v⁻¹ * d.t) by group]
  exact mul_mem ((by rw [Z₂_eq_sup]; exact le_sup_right : d.ZX₄ ≤ d.Z₂) hc) hθ

theorem card_A₁V₂
    (h : d.Hyp) :
    Nat.card (d.A₁ ⊔ d.V₂ : Subgroup G) = 2 ^ 10 := by
  have hinf : d.V₂ ⊓ d.A₁ = d.Z₂ := by
    refine le_antisymm (fun x hx => ?_) (le_inf h.Z₂_le_V₂ Z₂_le_A₁)
    rw [← h.V₂_inf_H]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1,
      h.L_le_H (d.pull_le_L _ (Subgroup.mem_inf.1 hx).2)⟩
  have e := card_sup_mul_card_inf_of_le_normalizer d.V₂ d.A₁ h.A₁_le_normalizer_V₂
  rw [hinf, sup_comm, h.card_V₂, d.card_A₁, card_Z₂] at e
  norm_num at e ⊢
  omega

theorem sec4_13_4
    (h : d.Hyp) :
    (∀ u ∈ d.D₃, u * d.t * u⁻¹ * d.t ∈ (d.X₃ ⊔ d.X₄) ⊔ d.W) ∧
      (∀ a ∈ d.X₃ ⊔ d.X₄, ∃ u ∈ d.D₃, ∃ w ∈ d.W, u * d.t * u⁻¹ * d.t = a * w) ∧
      (∀ x ∈ d.D₁, (x ∈ d.D₃ ↔ x * d.t * x⁻¹ * d.t ∈ (d.X₃ ⊔ d.X₄) ⊔ d.W)) ∧
      (∀ x ∈ d.D₁, (x ∈ d.A₁ ⊔ d.V₂ ↔ x * d.t * x⁻¹ * d.t ∈ d.Z₂ ⊔ d.W)) ∧
      Nat.card d.D₃ = 2 ^ 12 ∧ Nat.card (d.A₁ ⊔ d.V₂ : Subgroup G) = 2 ^ 10 := by
  refine ⟨fun _ hu => h.crossed_mem_of_mem_D₃ hu, fun _ ha => h.exists_D₃_conj_t ha,
    fun x hx => ⟨h.crossed_mem_of_mem_D₃, fun hθ => h.mem_D₃_of_crossed_mem hx hθ⟩,
    fun x hx => ⟨fun hA => mem_sup_left (h.crossed_mem_Z₂_of_mem_A₁V₂ hA),
      h.mem_A₁V₂_of_crossed_mem hx⟩, h.card_D₃, h.card_A₁V₂⟩

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
