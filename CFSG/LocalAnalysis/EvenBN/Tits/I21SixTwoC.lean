module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixTwoC3
public import CFSG.LocalAnalysis.EvenBN.Tits.I21SixTwoC4
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoTwoGroup

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

open Subgroup CFSG.Open

variable {G : Type*} [Group G]

theorem relIndex_eq_two [Finite G] {P T : Subgroup G} (hle : T ≤ P) (hdvd : T.relIndex P ∣ 2)
    (hne : T ≠ P) : T.relIndex P = 2 := by
  have h1 : T.relIndex P ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hPT
    exact hne (le_antisymm hle hPT)
  have h0 : T.relIndex P ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem exists_mem_not_mem {P T L : Subgroup G} (hle : T ≤ P) (hrel : T.relIndex P = 2)
    (hML : (P ⊓ L).relIndex P = 2) {t : G} (htT : t ∈ T) (htL : t ∉ L) :
    ∃ m ∈ P ⊓ L, m ∉ T := by
  by_contra hcon
  have hle' : P ⊓ L ≤ T := fun g hg => by_contra fun hgT => hcon ⟨g, hg, hgT⟩
  have := Subgroup.relIndex_mul_relIndex (P ⊓ L) T P hle' hle
  rw [hML, hrel] at this
  have h1 : (P ⊓ L).relIndex T = 1 := by omega
  rw [Subgroup.relIndex_eq_one] at h1
  exact htL (h1 htT).2

theorem reflection_sq {t x : G} (hty : t * x * t⁻¹ = x⁻¹) (ht2 : t ^ 2 = 1) (i : ℕ) :
    (x ^ i * t) ^ 2 = 1 := by
  calc (x ^ i * t) ^ 2 = x ^ i * (t * x * t⁻¹) ^ i * t ^ 2 := by
        rw [conj_pow, pow_two (x ^ i * t), pow_two t]; group
    _ = 1 := by rw [hty, ht2, inv_pow]; group

theorem mk_config {P T L : Subgroup G} {y w m : G} (ht0 : T0 y w)
    (hwy : w * y * w⁻¹ ∈ zpowers y) (hle : T ≤ P) (hrel : T.relIndex P = 2)
    (hcl : T ⊓ L = closure ({y, w} : Set G)) (hmP : m ∈ P) (hmL : m ∈ L) (hmT : m ∉ T) :
    Config (P ⊓ L) y w m := by
  have hy : y ∈ T ⊓ L := by rw [hcl]; exact subset_closure (by simp)
  have hw : w ∈ T ⊓ L := by rw [hcl]; exact subset_closure (by simp)
  obtain ⟨hyT, hyL⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨hwT, hwL⟩ := Subgroup.mem_inf.mp hw
  refine ⟨ht0, hwy, Subgroup.mem_inf.mpr ⟨hle hyT, hyL⟩, Subgroup.mem_inf.mpr ⟨hle hwT, hwL⟩,
    Subgroup.mem_inf.mpr ⟨hmP, hmL⟩, ?_, ?_, ?_⟩
  · intro hm
    rw [← hcl] at hm
    exact hmT (Subgroup.mem_inf.mp hm).1
  · rw [← hcl]
    exact Subgroup.mem_inf.mpr ⟨sq_mem_of_relIndex_two hrel hmP, pow_mem hmL 2⟩
  · intro g hg
    obtain ⟨hgP, hgL⟩ := Subgroup.mem_inf.mp hg
    by_cases hgT : g ∈ T
    · left
      rw [← hcl]
      exact Subgroup.mem_inf.mpr ⟨hgT, hgL⟩
    · right
      rw [← hcl]
      refine Subgroup.mem_inf.mpr ⟨?_, mul_mem hgL (inv_mem hmL)⟩
      exact (mul_mem_iff_of_relIndex_two hrel hgP (inv_mem hmP)).mpr ⟨fun h' => absurd h' hgT,
        fun h' => absurd (inv_mem_iff.mp h') hmT⟩

theorem D_cases {t x g : G} (hty : t * x * t⁻¹ = x⁻¹) (ht2 : t ^ 2 = 1)
    (hg : g ∈ closure ({t, x} : Set G)) : g ∈ zpowers x ∨ ∃ ρ ∈ zpowers x, g = ρ * t := by
  rw [Set.pair_comm] at hg
  exact mem_closure_pair_cases (by rw [hty]; exact inv_mem (mem_zpowers x))
    (by rw [ht2]; exact one_mem _) hg

end CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

open Subgroup CFSG.Open

section Shape

variable {G : Type} [Group G] [Finite G] {t u x u₀ : G} {P T : Subgroup G}
  (hsh : TwoGroupShape P t (u ^ 2) 3 x u₀ T)

include hsh

theorem shape_x_order : orderOf x = 4 := by simpa using hsh.ord_x

theorem shape_x_sq : x ^ 2 = u ^ 2 := by simpa using hsh.z_eq

theorem shape_x_pow_four : x ^ 4 = 1 := by
  rw [← shape_x_order hsh]; exact pow_orderOf_eq_one x

theorem shape_u₀_pow_four : u₀ ^ 4 = 1 := by
  rw [← hsh.ord_u]; exact pow_orderOf_eq_one u₀

theorem shape_t_mem : t ∈ T := by rw [hsh.T_eq]; exact subset_closure (by simp)

theorem shape_x_mem : x ∈ T := by rw [hsh.T_eq]; exact subset_closure (by simp)

theorem shape_u₀_mem : u₀ ∈ T := by rw [hsh.T_eq]; exact subset_closure (by simp)

theorem shape_D_normal {p d : G} (hp : p ∈ P) (hd : d ∈ closure ({t, x} : Set G)) :
    p * d * p⁻¹ ∈ closure ({t, x} : Set G) := by
  rw [← hsh.D_eq] at hd ⊢
  refine Subgroup.closure_induction
    (p := fun d _ => p * d * p⁻¹ ∈ closure {s : G | s ∈ P ∧ ∃ g : G, g * t * g⁻¹ = s})
    ?_ ?_ ?_ ?_ hd
  · rintro d ⟨hdP, g, hg⟩
    exact subset_closure ⟨mul_mem (mul_mem hp hdP) (inv_mem hp), p * g, by rw [← hg]; group⟩
  · simp
  · intro a b _ _ ha hb
    have : p * (a * b) * p⁻¹ = (p * a * p⁻¹) * (p * b * p⁻¹) := by group
    rw [this]
    exact mul_mem ha hb
  · intro a _ ha
    have e : p * a⁻¹ * p⁻¹ = (p * a * p⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

theorem shape_u₀_not_mem (h : SecTwoHyp G t u) : u₀ ∉ zpowers x := by
  intro hmem
  have hD : zpowers x ≤ closure ({t, x} : Set G) := (zpowers_le).mpr (subset_closure (by simp))
  have h1 : u₀ ∈ zpowers u₀ ⊓ closure ({t, x} : Set G) := ⟨mem_zpowers u₀, hD hmem⟩
  rw [hsh.inf_eq] at h1
  obtain ⟨i, hi, hi'⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) h.z_sq h1
  have : u₀ ^ 2 = 1 := by
    rw [hi', ← pow_mul, mul_comm, pow_mul, h.z_sq, one_pow]
  exact h.z_ne_one (hsh.sq_u.symm.trans this)

theorem shape_q_sq (h : SecTwoHyp G t u) : (t * u₀) ^ 2 = x ^ 2 := by
  rw [(show Commute t u₀ from hsh.comm_ut.symm).mul_pow, h.t_sq, one_mul, hsh.sq_u,
    shape_x_sq hsh]

theorem shape_q_conj : (t * u₀) * x * (t * u₀)⁻¹ = x⁻¹ := by
  calc (t * u₀) * x * (t * u₀)⁻¹ = t * (u₀ * x * u₀⁻¹) * t⁻¹ := by group
    _ = t * x * t⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr hsh.comm_ux]
    _ = x⁻¹ := hsh.inv_x

theorem shape_q_not_mem (h : SecTwoHyp G t u) : t * u₀ ∉ zpowers x := by
  intro hmem
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
  have hc : x ^ k * x = x * x ^ k := ((Commute.refl x).zpow_left k).eq
  have h1 : x ^ k * x * (x ^ k)⁻¹ = x := by rw [hc]; group
  rw [hk, shape_q_conj hsh] at h1
  apply h.z_ne_one
  rw [← shape_x_sq hsh, pow_two]
  exact inv_eq_iff_mul_eq_one.mp h1

theorem shape_t_q_comm : t * (t * u₀) = (t * u₀) * t := by
  calc t * (t * u₀) = t * (u₀ * t) := by rw [hsh.comm_ut]
    _ = (t * u₀) * t := by rw [mul_assoc]

end Shape

section Action

variable {G : Type} [Group G] [Finite G] {t u x u₀ : G} {P T : Subgroup G}
  (h : SecTwoHyp G t u) (hP : IsPGroup 2 P) (hRP : secTwoR t u ≤ P)
  (hsh : TwoGroupShape P t (u ^ 2) 3 x u₀ T)

include h hP hRP hsh

theorem shape_z_conj {g : G} (hg : g ∈ P) : g * u ^ 2 * g⁻¹ = u ^ 2 :=
  mul_inv_eq_iff_eq_mul.mpr (h.z_mem_center hP hRP hg)

theorem shape_action_t {m : G} (hmP : m ∈ P) (hmT : m ∉ T) :
    ∃ ε : ℕ, ε % 2 = 1 ∧ m * t * m⁻¹ = x ^ ε * t := by
  have hx4 := shape_x_order hsh
  have hx4' := shape_x_pow_four hsh
  have hty : t * x * t⁻¹ = x⁻¹ := hsh.inv_x
  have hxz := shape_x_sq hsh
  have htP : t ∈ P := hsh.T_le (shape_t_mem hsh)
  have hxT := shape_x_mem hsh
  have hxP : x ∈ P := hsh.T_le hxT
  have hmtD : m * t * m⁻¹ ∈ closure ({t, x} : Set G) :=
    hsh.class_le_D m (mul_mem (mul_mem hmP htP) (inv_mem hmP))
  rcases D_cases hty h.t_sq hmtD with hg | ⟨ρ, hρ, hg⟩
  · exfalso
    obtain ⟨i, hi, hi'⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) hx4' hg
    have hsq : (m * t * m⁻¹) ^ 2 = 1 := by rw [conj_pow, h.t_sq]; group
    rw [hi', ← pow_mul] at hsq
    have h1 : (i * 2) % 4 = 0 % 4 := by
      rw [← pow_eq_pow_iff_of_orderOf_four hx4, pow_zero]; exact hsq
    have h2 : i = 0 ∨ i = 2 := by omega
    rcases h2 with rfl | rfl
    · apply h.t_ne_one
      have h3 : m * t * m⁻¹ = 1 := by rw [hi', pow_zero]
      have h4 : m * t = m := mul_inv_eq_one.mp h3
      exact mul_left_cancel (h4.trans (mul_one m).symm)
    · apply h.sq_ne
      have h3 : m * t * m⁻¹ = u ^ 2 := by rw [hi', hxz]
      have h4 : m * t = u ^ 2 * m := mul_inv_eq_iff_eq_mul.mp h3
      have h5 : m * u ^ 2 = u ^ 2 * m := mul_inv_eq_iff_eq_mul.mp (shape_z_conj h hP hRP hsh hmP)
      exact (mul_left_cancel (h4.trans h5.symm)).symm
  · obtain ⟨i, hi, rfl⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) hx4' hρ
    refine ⟨i, ?_, hg⟩
    by_contra hodd
    have hev : i = 0 ∨ i = 2 := by omega
    have hsx : SemiconjBy t x x⁻¹ := mul_inv_eq_iff_eq_mul.mp hty
    have htx : x * t * x⁻¹ = x ^ 2 * t := by
      have h1 : t * x⁻¹ = x * t := by simpa using hsx.inv_right.eq
      calc x * t * x⁻¹ = x * (t * x⁻¹) := by group
        _ = x ^ 2 * t := by rw [h1, pow_two, mul_assoc]
    rcases hev with rfl | rfl
    · apply hmT
      apply hsh.R_le
      refine Subgroup.mem_inf.mpr ⟨?_, hmP⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : m * t * m⁻¹ = t := by rw [hg]; simp
      exact mul_inv_eq_iff_eq_mul.mp h1
    · have h1 : (x⁻¹ * m) * t * (x⁻¹ * m)⁻¹ = t := by
        calc (x⁻¹ * m) * t * (x⁻¹ * m)⁻¹ = x⁻¹ * (m * t * m⁻¹) * x := by group
          _ = x⁻¹ * (x * t * x⁻¹) * x := by rw [hg, htx]
          _ = t := by group
      have hmem : x⁻¹ * m ∈ T := by
        apply hsh.R_le
        refine Subgroup.mem_inf.mpr ⟨?_, mul_mem (inv_mem hxP) hmP⟩
        rw [mem_centralizer_singleton_iff]
        exact mul_inv_eq_iff_eq_mul.mp h1
      exact hmT (by simpa using mul_mem hxT hmem)

theorem shape_action_x {m : G} (hmP : m ∈ P) :
    m * x * m⁻¹ = x ∨ m * x * m⁻¹ = x⁻¹ := by
  have hx4 := shape_x_order hsh
  have hx4' := shape_x_pow_four hsh
  have hxz := shape_x_sq hsh
  have hD : m * x * m⁻¹ ∈ closure ({t, x} : Set G) :=
    shape_D_normal hsh hmP (subset_closure (by simp))
  have hsq : (m * x * m⁻¹) ^ 2 = x ^ 2 := by
    rw [conj_pow, hxz]; exact shape_z_conj h hP hRP hsh hmP
  rcases D_cases hsh.inv_x h.t_sq hD with hg | ⟨ρ, hρ, hg⟩
  · obtain ⟨i, hi, hi'⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) hx4' hg
    rw [hi', ← pow_mul] at hsq
    have h1 : (i * 2) % 4 = 2 % 4 := (pow_eq_pow_iff_of_orderOf_four hx4).mp hsq
    have h2 : i = 1 ∨ i = 3 := by omega
    rcases h2 with rfl | rfl
    · left; rw [hi', pow_one]
    · right; rw [hi', inv_eq_pow_three hx4']
  · exfalso
    obtain ⟨i, hi, rfl⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) hx4' hρ
    rw [hg, reflection_sq hsh.inv_x h.t_sq i, hxz] at hsq
    exact h.z_ne_one hsq.symm

theorem shape_action_u₀ {m : G} (hmP : m ∈ P) :
    m * u₀ * m⁻¹ = u₀ ∨ m * u₀ * m⁻¹ = u₀⁻¹ := by
  have hu₀4' := shape_u₀_pow_four hsh
  have hmem : m * u₀ * m⁻¹ ∈ zpowers u₀ := hsh.U_norm m hmP u₀ (mem_zpowers u₀)
  have hsq : (m * u₀ * m⁻¹) ^ 2 = u₀ ^ 2 := by
    rw [conj_pow, hsh.sq_u]; exact shape_z_conj h hP hRP hsh hmP
  obtain ⟨i, hi, hi'⟩ := exists_pow_lt_of_mem_zpowers (by norm_num) hu₀4' hmem
  rw [hi', ← pow_mul] at hsq
  have h1 : (i * 2) % 4 = 2 % 4 := (pow_eq_pow_iff_of_orderOf_four hsh.ord_u).mp hsq
  have h2 : i = 1 ∨ i = 3 := by omega
  rcases h2 with rfl | rfl
  · left; rw [hi', pow_one]
  · right; rw [hi', inv_eq_pow_three hu₀4']

theorem shape_action_q {m : G} (hmP : m ∈ P) {ε : ℕ} (hε : ε % 2 = 1)
    (hmt : m * t * m⁻¹ = x ^ ε * t) (hmu : m * u₀ * m⁻¹ = u₀ ∨ m * u₀ * m⁻¹ = u₀⁻¹) :
    ∃ κ : ℕ, κ % 2 = 1 ∧ m * (t * u₀) * m⁻¹ = x ^ κ * (t * u₀) := by
  have e : m * (t * u₀) * m⁻¹ = (m * t * m⁻¹) * (m * u₀ * m⁻¹) := by group
  rcases hmu with hu | hu
  · refine ⟨ε, hε, ?_⟩
    rw [e, hmt, hu, mul_assoc]
  · refine ⟨ε + 2, by omega, ?_⟩
    have hu' : u₀⁻¹ = u₀ * x ^ 2 := by
      rw [inv_eq_pow_three (shape_u₀_pow_four hsh), show (3 : ℕ) = 2 + 1 from rfl, pow_succ',
        hsh.sq_u, shape_x_sq hsh]
    have hqP : t * u₀ ∈ P := mul_mem (hsh.T_le (shape_t_mem hsh)) (hsh.T_le (shape_u₀_mem hsh))
    have hzq : (t * u₀) * x ^ 2 = x ^ 2 * (t * u₀) := by
      rw [shape_x_sq hsh]
      exact mul_inv_eq_iff_eq_mul.mp (shape_z_conj h hP hRP hsh hqP)
    calc m * (t * u₀) * m⁻¹ = (m * t * m⁻¹) * (m * u₀ * m⁻¹) := e
      _ = x ^ ε * t * (u₀ * x ^ 2) := by rw [hmt, hu, hu']
      _ = x ^ ε * ((t * u₀) * x ^ 2) := by group
      _ = x ^ ε * (x ^ 2 * (t * u₀)) := by rw [hzq]
      _ = x ^ (ε + 2) * (t * u₀) := by rw [pow_add]; group

end Action

end CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.I21.SixTwoC

variable {G : Type} [Group G] [Finite G] {t u x : G}

theorem sec622_six_two_c (h : SecTwoHyp G t u) {L : Subgroup G} (hLn : L.Normal)
    (htL : t ∉ L) {P : Subgroup G} (hP : IsPGroup 2 P) (hRP : secTwoR t u ≤ P)
    (hPL : (P ⊓ L).relIndex P = 2) {T : Subgroup G} {x u₀ : G}
    (hsh : TwoGroupShape P t (u ^ 2) 3 x u₀ T) (hTP : T ≠ P)
    (hTL : T ⊓ L = closure {x, u₀} ∨ T ⊓ L = closure {x, t * u₀}) :
    IsMulCommutative (P ⊓ L : Subgroup G) ∨ Sec622ProdDihedral (P ⊓ L) 3 ∨
      Sec622CentralInv (P ⊓ L) ∨ Sec622Order16 (P ⊓ L) ∨
      Nonempty (↥(P ⊓ L) ≃* SemidihedralGroup 4) ∨ Sec622UniqueInv (P ⊓ L) := by
  have hrel : T.relIndex P = 2 := relIndex_eq_two hsh.T_le hsh.T_idx hTP
  obtain ⟨m, hmML, hmT⟩ := exists_mem_not_mem hsh.T_le hrel hPL (shape_t_mem hsh) htL
  obtain ⟨hmP, hmL⟩ := Subgroup.mem_inf.mp hmML
  obtain ⟨ε, hε, hmt⟩ := shape_action_t h hP hRP hsh hmP hmT
  have hmx := shape_action_x h hP hRP hsh hmP
  have hmu := shape_action_u₀ h hP hRP hsh hmP
  have ht0 : T0 x u₀ :=
    ⟨shape_x_order hsh, by rw [hsh.sq_u, shape_x_sq hsh], shape_u₀_not_mem hsh h⟩
  rcases hTL with hTL | hTL
  ·
    have hwy : u₀ * x * u₀⁻¹ ∈ zpowers x := by
      rw [mul_inv_eq_iff_eq_mul.mpr hsh.comm_ux]; exact mem_zpowers x
    have c := mk_config ht0 hwy hsh.T_le hrel hTL hmP hmL hmT
    rcases case_one c hsh.comm_ux.symm hsh.inv_x hsh.comm_ut.symm hε hmt hmx hmu with
      h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  ·
    have ht0' : T0 x (t * u₀) :=
      ⟨shape_x_order hsh, shape_q_sq hsh h, shape_q_not_mem hsh h⟩
    have hwy : (t * u₀) * x * (t * u₀)⁻¹ ∈ zpowers x := by
      rw [shape_q_conj hsh]; exact inv_mem (mem_zpowers x)
    have c := mk_config ht0' hwy hsh.T_le hrel hTL hmP hmL hmT
    obtain ⟨κ, hκ, hmq⟩ := shape_action_q h hP hRP hsh hmP hε hmt hmu
    exact Or.inr (Or.inr (Or.inr (Or.inr (case_two c (shape_q_conj hsh) (shape_t_q_comm hsh)
      hsh.inv_x hε hκ hmt hmq hmx))))

end CFSG.LocalAnalysis.EvenBN.Tits
