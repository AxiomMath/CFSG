module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.PZAbs
public import CFSG.LocalAnalysis.EvenBN.Tits.S56V2
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N2

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.PZ

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits
  CFSG.LocalAnalysis.EvenBN.Tits.Data
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


structure Twist (d : Data G) (a : G → G) : Prop where
  mem_E : ∀ v ∈ d.s56V, a v ∈ d.E
  mul : ∀ u ∈ d.s56V, ∀ v ∈ d.s56V, a (u * v) = a u * a v
  conj : ∀ g ∈ d.M, g * d.t = d.t * g → ∀ v ∈ d.s56V, a (g * v * g⁻¹) = g * a v * g⁻¹
  triv : ∀ e ∈ d.E, a e = 1
  mem_z : ∀ v ∈ d.s56V, v * v * a v ∈ zpowers d.z

@[expose] def qq (a : G → G) (v : G) : G := v * v * a v

section QForm

variable {a : G → G}

theorem Twist.qq_mem (tw : Twist d a) {v : G} (hv : v ∈ d.s56V) : qq a v ∈ zpowers d.z :=
  tw.mem_z v hv

theorem Twist.qq_one (tw : Twist d a) : qq a 1 = 1 := by
  unfold qq
  rw [tw.triv 1 (one_mem _)]
  simp

theorem Twist.qq_mul_E (tw : Twist d a) (h49 : d.Thm49Statement) (hd : d.Hyp) {v e : G}
    (hv : v ∈ d.s56V) (he : e ∈ d.E) : qq a (v * e) = qq a v := by
  have heV : e ∈ d.s56V := hd.s56_E_le_V h49 he
  have hve : v * e = e * v := s56_V_comm_E hv he
  have hee : e * e = 1 := hd.s56_E_sq he
  unfold qq
  rw [tw.mul v hv e heV, tw.triv e he, mul_one]
  calc v * e * (v * e) * a v = v * (e * v) * e * a v := by group
    _ = v * (v * e) * e * a v := by rw [← hve]
    _ = v * v * (e * e) * a v := by group
    _ = v * v * a v := by rw [hee, mul_one]

theorem Twist.qq_mul (tw : Twist d a) (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    {u v : G} (hu : u ∈ d.s56V) (hv : v ∈ d.s56V) :
    qq a (u * v) = (v * u * v⁻¹ * u⁻¹) * (qq a u * qq a v) := by
  obtain ⟨c, hcdef⟩ : ∃ c, c = v * u * v⁻¹ * u⁻¹ := ⟨_, rfl⟩
  have hcz : c ∈ zpowers d.z := hcdef ▸ hd.s56_V_comm_mem h49 hz hv hu
  have hcE : c ∈ d.E := hd.s56_zpowers_le_E hcz
  have hcu : u * c = c * u := s56_V_comm_E hu hcE
  have hvu : v * u = c * u * v := by rw [hcdef]; group
  have hau : a u * v = v * a u := (s56_V_comm_E hv (tw.mem_E u hu)).symm
  have hauvv : a u * (v * v) = v * v * a u := by
    calc a u * (v * v) = (a u * v) * v := by group
      _ = (v * a u) * v := by rw [hau]
      _ = v * (a u * v) := by group
      _ = v * (v * a u) := by rw [hau]
      _ = v * v * a u := by group
  rw [← hcdef]
  unfold qq
  rw [tw.mul u hu v hv]
  calc u * v * (u * v) * (a u * a v) = u * (v * u) * v * (a u * a v) := by group
    _ = u * (c * u * v) * v * (a u * a v) := by rw [hvu]
    _ = (u * c) * u * v * v * (a u * a v) := by group
    _ = c * u * u * v * v * (a u * a v) := by rw [hcu]
    _ = c * (u * u * (v * v) * a u * a v) := by group
    _ = c * (u * u * (v * v * a u) * a v) := by group
    _ = c * (u * u * (a u * (v * v)) * a v) := by rw [hauvv]
    _ = c * (u * u * a u * (v * v * a v)) := by group

theorem Twist.qq_conj (tw : Twist d a) (hd : d.Hyp) {g v : G} (hgM : g ∈ d.M)
    (hgt : g * d.t = d.t * g) (hv : v ∈ d.s56V) : qq a (g * v * g⁻¹) = qq a v := by
  have hq := tw.qq_mem hv
  have hg : g * qq a v = qq a v * g := hd.s56_M_comm_zpowers hgM hq
  unfold qq at hg ⊢
  rw [tw.conj g hgM hgt v hv]
  calc g * v * g⁻¹ * (g * v * g⁻¹) * (g * a v * g⁻¹) = g * (v * v * a v) * g⁻¹ := by group
    _ = v * v * a v := by rw [hg]; group

theorem Twist.qq_eq_of_eps_eq (tw : Twist d a) (h49 : d.Thm49Statement) (hd : d.Hyp) {v w : G}
    (hv : v ∈ d.s56V) (hw : w ∈ d.s56V) (h : d.s56Eps v = d.s56Eps w) : qq a v = qq a w := by
  have hwi : w⁻¹ ∈ d.s56V := inv_mem hw
  have hwv : w⁻¹ * v ∈ d.s56V := mul_mem hwi hv
  have hε1 : d.s56Eps (w⁻¹ * v) = 1 := by
    rw [hd.s56_eps_mul_Q2' hwi.2 hv.2, hd.s56_eps_inv_Q2 hw.2, h]
    exact hd.s56_E_sq (hd.s56_V_eps_mem_E hw)
  have hE : w⁻¹ * v ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 hwv).1 hε1
  have e : v = w * (w⁻¹ * v) := by group
  rw [e, tw.qq_mul_E h49 hd hw hE]

theorem Twist.qq_orbit (tw : Twist d a) (h49 : d.Thm49Statement) (hd : d.Hyp) {u v g : G}
    (hu : u ∈ d.s56V) (hu1 : qq a u = 1) (hv : v ∈ d.s56V) (hgM : g ∈ d.M)
    (hgt : g * d.t = d.t * g) (h : d.s56Eps v = g * d.s56Eps u * g⁻¹) : qq a v = 1 := by
  have hu' : g * u * g⁻¹ ∈ d.s56V := hd.s56_V_conj_mem h49 hgM hu
  have hε : d.s56Eps v = d.s56Eps (g * u * g⁻¹) := by rw [hd.s56_eps_conj hgt, h]
  rw [tw.qq_eq_of_eps_eq h49 hd hv hu' hε, tw.qq_conj hd hgM hgt hu, hu1]

end QForm

section Long

theorem fiveData (hd : d.Hyp) : FiveData d.E d.x₅ d.z (d.pv 11) where
  comm a ha b hb := hd.s56_E_comm ha hb
  sq e he := hd.s56_E_sq he
  norm e he := (mem_normalizer_iff.1 (hd.s56_ME hd.s56_x5_mem_M) e).1 he
  x5 := by rw [← hd.s56_orderOf_x5]; exact pow_orderOf_eq_one _
  z_mem := hd.s56_z_mem_E
  z_ne := hd.s56_z_ne_one
  xz := hd.s56_x5_comm_z
  cent e he hx := by
    rcases hd.s56_mem_zpowers_z (hd.s56_E_cent_x5 he hx.symm) with h | h
    · exact Or.inl h
    · exact Or.inr h
  ℓ_mem := hd.s56_zL_inter_A_le_E ((hd.s56_pv11_mem_Lg).1)
  ℓ_ne_one h := (zL_vL_disjoint d).1 (h ▸ (hd.s56_pv11_mem_Lg).1.1)
  ℓ_ne_z h := (hd.s56_pv11_mem_Lg).2 (Set.mem_singleton_iff.2 h)

theorem cj_mem_Lg (hd : d.Hyp) (i : ℕ) : cj d.x₅ (d.pv 11) i ∈ d.s56Lg := by
  have horb : d.s56Lg = {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 11 * x⁻¹ = y} :=
    ((hd.orbits_A).2.2.1).symm
  rw [horb]
  refine ⟨d.x₅ ^ i, mem_inf.2 ⟨pow_mem hd.s56_x5_mem_M i, ?_⟩, rfl⟩
  rw [mem_centralizer_singleton_iff]
  exact (Commute.pow_left (show Commute d.x₅ d.t from hd.s56_x5_comm_t) i).eq

theorem Lg_mul_z (hd : d.Hyp) {e : G} (he : e ∈ d.s56Lg) : e * d.z ∈ d.s56Lg :=
  (s56SqueezeData hd).Lg_z ⟨e, d.s56_A_le_M he.1.2⟩ he

theorem cover_E (hd : d.Hyp) {e : G} (he : e ∈ d.E) :
    e = 1 ∨ e = d.z ∨ e ∈ d.s56Lg ∨ e ∈ d.s56Sg := by
  have := (s56SqueezeData hd).cover ⟨e, d.s56_E_le_M he⟩ (Subgroup.mem_subgroupOf.2 he)
  rcases this with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem cj_ne (hd : d.Hyp) (i : ℕ) :
    cj d.x₅ (d.pv 11) i ≠ 1 ∧ cj d.x₅ (d.pv 11) i ≠ d.z := by
  have h := cj_mem_Lg hd i
  exact ⟨fun h1 => (zL_vL_disjoint d).1 (h1 ▸ h.1.1), fun h1 => h.2 (Set.mem_singleton_iff.2 h1)⟩

theorem Lg_eq (hd : d.Hyp) :
    d.s56Lg = {y | ∃ k : ℕ, k < 5 ∧ (y = cj d.x₅ (d.pv 11) k ∨ y = cj d.x₅ (d.pv 11) k * d.z)} := by
  classical
  have fd := fiveData hd
  let f : Fin 5 × Bool → G := fun p => cj d.x₅ (d.pv 11) p.1 * (if p.2 then d.z else 1)
  have hz2 := fd.z_sq
  have key : ∀ (i j : ℕ), i < 5 → j < 5 → ∀ w w' : G, (w = 1 ∨ w = d.z) → (w' = 1 ∨ w' = d.z) →
      cj d.x₅ (d.pv 11) i * w = cj d.x₅ (d.pv 11) j * w' → i = j ∧ w = w' := by
    intro i j hi hj w w' hw hw' h
    by_cases hij : i = j
    · subst hij
      exact ⟨rfl, mul_left_cancel h⟩
    · exfalso
      have hww := fd.w_sq hw
      have hww' := fd.w_sq hw'
      have h1 : cj d.x₅ (d.pv 11) i = cj d.x₅ (d.pv 11) j * w' * w⁻¹ := by
        rw [← h]; group
      have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
      have hcomm : ∀ y ∈ ({1, d.z} : Set G), cj d.x₅ (d.pv 11) j * y = y * cj d.x₅ (d.pv 11) j := by
        rintro y (rfl | rfl)
        · simp
        · exact fd.comm _ (fd.mem j) _ fd.z_mem
      have hprod : cj d.x₅ (d.pv 11) i * cj d.x₅ (d.pv 11) j = w' * w := by
        rw [h1, hwinv]
        have hw'c := hcomm w' (by rcases hw' with h | h <;> simp [h])
        have hwc := hcomm w (by rcases hw with h | h <;> simp [h])
        calc cj d.x₅ (d.pv 11) j * w' * w * cj d.x₅ (d.pv 11) j
            = cj d.x₅ (d.pv 11) j * w' * (w * cj d.x₅ (d.pv 11) j) := by group
          _ = cj d.x₅ (d.pv 11) j * w' * (cj d.x₅ (d.pv 11) j * w) := by rw [← hwc]
          _ = cj d.x₅ (d.pv 11) j * (w' * cj d.x₅ (d.pv 11) j) * w := by group
          _ = cj d.x₅ (d.pv 11) j * (cj d.x₅ (d.pv 11) j * w') * w := by rw [← hw'c]
          _ = (cj d.x₅ (d.pv 11) j * cj d.x₅ (d.pv 11) j) * (w' * w) := by group
          _ = w' * w := by rw [fd.sq_cj j, one_mul]
      have hne := fd.mul_ne hi hj hij
      rcases hw with rfl | rfl <;> rcases hw' with rfl | rfl
      · simp only [mul_one] at hprod; exact hne.1 hprod
      · simp only [mul_one, one_mul] at hprod; exact hne.2 hprod
      · simp only [mul_one, one_mul] at hprod; exact hne.2 hprod
      · exact hne.1 (hprod.trans hz2)
  have hf : Function.Injective f := by
    rintro ⟨i, bi⟩ ⟨j, bj⟩ h
    have hi := i.2
    have hj := j.2
    have hwi : (if bi then d.z else 1) = 1 ∨ (if bi then d.z else 1) = d.z := by
      cases bi <;> simp
    have hwj : (if bj then d.z else 1) = 1 ∨ (if bj then d.z else 1) = d.z := by
      cases bj <;> simp
    obtain ⟨hij, hw⟩ := key i j hi hj _ _ hwi hwj h
    have hij' : i = j := Fin.ext hij
    subst hij'
    have : bi = bj := by
      cases bi <;> cases bj <;> simp at hw ⊢
      · exact fd.z_ne hw.symm
      · exact fd.z_ne hw
    rw [this]
  have hrange : Set.range f ⊆ d.s56Lg := by
    rintro _ ⟨⟨i, b⟩, rfl⟩
    cases b
    · simpa [f] using cj_mem_Lg hd i
    · simpa [f] using Lg_mul_z hd (cj_mem_Lg hd i)
  have hcard : d.s56Lg.ncard ≤ (Set.range f).ncard := by
    rw [Set.ncard_range_of_injective hf]
    have h10 : d.s56Lg.ncard = 10 := (hd.orbits_A).2.2.2.1
    rw [h10]
    simp
  have heq : Set.range f = d.s56Lg := Set.eq_of_subset_of_ncard_le hrange hcard (Set.toFinite _)
  rw [← heq]
  ext y
  constructor
  · rintro ⟨⟨i, b⟩, rfl⟩
    refine ⟨i, i.2, ?_⟩
    cases b
    · exact Or.inl (by simp [f])
    · exact Or.inr (by simp [f])
  · rintro ⟨k, hk, h | h⟩
    · exact ⟨(⟨k, hk⟩, false), by simp [f, h]⟩
    · exact ⟨(⟨k, hk⟩, true), by simp [f, h]⟩

theorem long_mul_short (hd : d.Hyp) {i j : ℕ} (hi : i < 5) (hj : j < 5) (hij : i ≠ j) :
    cj d.x₅ (d.pv 11) i * cj d.x₅ (d.pv 11) j ∈ d.s56Sg := by
  have fd := fiveData hd
  have hE : cj d.x₅ (d.pv 11) i * cj d.x₅ (d.pv 11) j ∈ d.E := mul_mem (fd.mem i) (fd.mem j)
  have hne := fd.mul_ne hi hj hij
  rcases cover_E hd hE with h1 | h1 | h1 | h1
  · exact absurd h1 hne.1
  · exact absurd h1 hne.2
  · exfalso
    rw [Lg_eq hd] at h1
    obtain ⟨k, hk, h2⟩ := h1
    have hci := fd.sq_cj i
    have hcj := fd.sq_cj j
    have hz2 := fd.z_sq
    by_cases hki : k = i
    · subst hki
      rcases h2 with h2 | h2
      ·
        have : cj d.x₅ (d.pv 11) j = 1 := by
          have h3 : cj d.x₅ (d.pv 11) k * cj d.x₅ (d.pv 11) j =
              cj d.x₅ (d.pv 11) k * 1 := by rw [h2, mul_one]
          exact mul_left_cancel h3
        exact (cj_ne hd j).1 this
      · have : cj d.x₅ (d.pv 11) j = d.z := by
          have h3 : cj d.x₅ (d.pv 11) k * cj d.x₅ (d.pv 11) j =
              cj d.x₅ (d.pv 11) k * d.z := h2
          exact mul_left_cancel h3
        exact (cj_ne hd j).2 this
    · by_cases hkj : k = j
      · subst hkj
        rcases h2 with h2 | h2
        · have : cj d.x₅ (d.pv 11) i = 1 := by
            have h3 : cj d.x₅ (d.pv 11) i * cj d.x₅ (d.pv 11) k =
                1 * cj d.x₅ (d.pv 11) k := by rw [h2, one_mul]
            exact mul_right_cancel h3
          exact (cj_ne hd i).1 this
        · have : cj d.x₅ (d.pv 11) i = d.z := by
            have h3 : cj d.x₅ (d.pv 11) i * cj d.x₅ (d.pv 11) k =
                d.z * cj d.x₅ (d.pv 11) k := by
              rw [h2]; exact fd.comm _ (fd.mem k) _ fd.z_mem
            exact mul_right_cancel h3
          exact (cj_ne hd i).2 this
      · have hnt := fd.no_triple hi hj hk hij (Ne.symm hkj) (Ne.symm hki)
        rcases h2 with h2 | h2
        · exact hnt.1 h2
        · exact hnt.2 h2
  · exact h1

end Long

section Core

variable {a : G → G}

theorem Twist.qq_mul_comm (tw : Twist d a) (h49 : d.Thm49Statement) (hd : d.Hyp)
    (hz : d.S56Z0 z₀) {u v : G} (hu : u ∈ d.s56V) (hv : v ∈ d.s56V) (hc : u * v = v * u) :
    qq a (u * v) = qq a u * qq a v := by
  rw [tw.qq_mul h49 hd hz hu hv]
  have h1 : v * u * v⁻¹ * u⁻¹ = 1 := by rw [← hc]; group
  rw [h1, one_mul]

theorem Twist.qq_eq_one (tw : Twist d a) (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (hz₀ : qq a z₀ = 1) (hu : ∃ u ∈ d.s56V, d.s56Eps u = d.pv 10 ∧ qq a u = 1) :
    ∀ v ∈ d.s56V, qq a v = 1 := by
  obtain ⟨u, huV, huε, hu1⟩ := hu
  have hxM := hd.s56_x5_mem_M
  have hxt := hd.s56_x5_comm_t
  have hpt : ∀ i : ℕ, d.x₅ ^ i * d.t = d.t * d.x₅ ^ i := fun i =>
    (Commute.pow_left (show Commute d.x₅ d.t from hxt) i).eq
  have short : ∀ v ∈ d.s56V, d.s56Eps v ∈ d.s56Sg → qq a v = 1 := by
    intro v hv hs
    have horb : d.s56Sg =
        {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 10 * x⁻¹ = y} :=
      ((hd.orbits_A).2.2.2.2.1).symm
    rw [horb] at hs
    obtain ⟨g, hg, hgε⟩ := hs
    exact tw.qq_orbit h49 hd huV hu1 hv (mem_inf.1 hg).1
      (mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2) (by rw [huε]; exact hgε.symm)
  have fd := fiveData hd
  obtain ⟨u₀, hu₀V, hu₀ε⟩ := hd.s56_V_eps_surj h49 hz (d.pv 11) fd.ℓ_mem
  obtain ⟨c, hcdef⟩ : ∃ c, c = qq a u₀ := ⟨_, rfl⟩
  have hcz : c ∈ zpowers d.z := hcdef ▸ tw.qq_mem hu₀V
  have hcc : c * c = 1 := hd.s56_zpowers_sq hcz
  let U : ℕ → G := fun i => cj d.x₅ u₀ i
  have hUV : ∀ i, U i ∈ d.s56V := fun i => hd.s56_V_conj_mem h49 (pow_mem hxM i) hu₀V
  have hUε : ∀ i, d.s56Eps (U i) = cj d.x₅ (d.pv 11) i := fun i => by
    show d.s56Eps (d.x₅ ^ i * u₀ * (d.x₅ ^ i)⁻¹) = d.x₅ ^ i * d.pv 11 * (d.x₅ ^ i)⁻¹
    rw [hd.s56_eps_conj (hpt i), hu₀ε]
  have hUq : ∀ i, qq a (U i) = c := fun i =>
    (tw.qq_conj hd (pow_mem hxM i) (hpt i) hu₀V).trans hcdef.symm
  have hC : ∀ i j, i < 5 → j < 5 → i ≠ j → Commute (U i) (U j) := by
    intro i j hi hj hij
    have hεij : d.s56Eps (U i * U j) = cj d.x₅ (d.pv 11) i * cj d.x₅ (d.pv 11) j := by
      rw [hd.s56_eps_mul_Q2' (hUV i).2 (hUV j).2, hUε, hUε]
    have hq1 : qq a (U i * U j) = 1 :=
      short _ (mul_mem (hUV i) (hUV j)) (by rw [hεij]; exact long_mul_short hd hi hj hij)
    rw [tw.qq_mul h49 hd hz (hUV i) (hUV j), hUq, hUq, hcc, mul_one] at hq1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hq1)).symm
  have hw : qq a (U 0 * U 1 * U 2 * U 3) = 1 := by
    have h1 : Commute (U 0) (U 1) := hC 0 1 (by norm_num) (by norm_num) (by norm_num)
    have h2 : Commute (U 0 * U 1) (U 2) :=
      Commute.mul_left (hC 0 2 (by norm_num) (by norm_num) (by norm_num))
        (hC 1 2 (by norm_num) (by norm_num) (by norm_num))
    have h3 : Commute (U 0 * U 1 * U 2) (U 3) :=
      Commute.mul_left (Commute.mul_left (hC 0 3 (by norm_num) (by norm_num) (by norm_num))
        (hC 1 3 (by norm_num) (by norm_num) (by norm_num)))
        (hC 2 3 (by norm_num) (by norm_num) (by norm_num))
    rw [tw.qq_mul_comm h49 hd hz (mul_mem (mul_mem (hUV 0) (hUV 1)) (hUV 2)) (hUV 3) h3.eq,
      tw.qq_mul_comm h49 hd hz (mul_mem (hUV 0) (hUV 1)) (hUV 2) h2.eq,
      tw.qq_mul_comm h49 hd hz (hUV 0) (hUV 1) h1.eq, hUq, hUq, hUq, hUq, hcc, one_mul, hcc]
  have hwV : U 0 * U 1 * U 2 * U 3 ∈ d.s56V :=
    mul_mem (mul_mem (mul_mem (hUV 0) (hUV 1)) (hUV 2)) (hUV 3)
  have hεw : d.s56Eps (U 0 * U 1 * U 2 * U 3) = cj d.x₅ (d.pv 11) 0 * cj d.x₅ (d.pv 11) 1 *
      cj d.x₅ (d.pv 11) 2 * cj d.x₅ (d.pv 11) 3 := by
    rw [hd.s56_eps_mul_Q2' (mul_mem (mul_mem (hUV 0) (hUV 1)) (hUV 2)).2 (hUV 3).2,
      hd.s56_eps_mul_Q2' (mul_mem (hUV 0) (hUV 1)).2 (hUV 2).2,
      hd.s56_eps_mul_Q2' (hUV 0).2 (hUV 1).2, hUε, hUε, hUε, hUε]
  have hR : cj d.x₅ (d.pv 11) 0 * cj d.x₅ (d.pv 11) 1 * cj d.x₅ (d.pv 11) 2 *
      cj d.x₅ (d.pv 11) 3 = (cj d.x₅ (d.pv 11) 0 * cj d.x₅ (d.pv 11) 1 * cj d.x₅ (d.pv 11) 2 *
        cj d.x₅ (d.pv 11) 3 * cj d.x₅ (d.pv 11) 4) * cj d.x₅ (d.pv 11) 4 := by
    rw [mul_assoc _ (cj d.x₅ (d.pv 11) 4) (cj d.x₅ (d.pv 11) 4), fd.sq_cj 4, mul_one]
  have hc1 : c = 1 := by
    rcases fd.prod_mem with hP | hP
    · have h := tw.qq_eq_of_eps_eq h49 hd hwV (hUV 4) (by rw [hεw, hR, hP, one_mul, hUε])
      rw [hw, hUq] at h
      exact h.symm
    · have hzU : z₀ * U 4 ∈ d.s56V := mul_mem hz.mem_V (hUV 4)
      have h := tw.qq_eq_of_eps_eq h49 hd hwV hzU (by
        rw [hεw, hR, hP, hd.s56_eps_mul_Q2' hz.mem_Q2 (hUV 4).2, hz.eps, hUε])
      rw [hw, tw.qq_mul_comm h49 hd hz hz.mem_V (hUV 4) (hz.comm_V (hUV 4)).symm, hz₀, hUq,
        one_mul] at h
      exact h.symm
  have hu₀1 : qq a u₀ = 1 := hcdef ▸ hc1
  have long : ∀ v ∈ d.s56V, d.s56Eps v ∈ d.s56Lg → qq a v = 1 := by
    intro v hv hl
    have horb : d.s56Lg =
        {y | ∃ x ∈ d.M ⊓ centralizer ({d.t} : Set G), x * d.pv 11 * x⁻¹ = y} :=
      ((hd.orbits_A).2.2.1).symm
    rw [horb] at hl
    obtain ⟨g, hg, hgε⟩ := hl
    exact tw.qq_orbit h49 hd hu₀V hu₀1 hv (mem_inf.1 hg).1
      (mem_centralizer_singleton_iff.1 (mem_inf.1 hg).2) (by rw [hu₀ε]; exact hgε.symm)
  intro v hv
  have hεE := hd.s56_V_eps_mem_E hv
  rcases cover_E hd hεE with h | h | h | h
  · have hvE : v ∈ d.E := (hd.s56_V_eps_eq_one_iff h49 hv).1 h
    have h2 := tw.qq_mul_E h49 hd (one_mem d.s56V) hvE
    rwa [one_mul, tw.qq_one] at h2
  · rw [tw.qq_eq_of_eps_eq h49 hd hv hz.mem_V (by rw [h, hz.eps]), hz₀]
  · exact long v hv h
  · exact short v hv h

end Core

section Instances

theorem twist_one (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀) (h1 : z₀ * z₀ = 1) :
    Twist d (fun _ : G => (1 : G)) where
  mem_E _ _ := one_mem _
  mul _ _ _ _ := by simp
  conj g _ _ v _ := by simp
  triv _ _ := rfl
  mem_z v hv := by simpa using hd.s56_V_sq_mem_of_sq_eq_one h49 hz h1 hv

theorem twist_eps (h49 : d.Thm49Statement) (hd : d.Hyp) (hz : d.S56Z0 z₀)
    (h1 : z₀ * z₀ = d.z) : Twist d d.s56Eps where
  mem_E _ hv := hd.s56_V_eps_mem_E hv
  mul _ hu _ hv := hd.s56_eps_mul_Q2' hu.2 hv.2
  conj _ _ hgt v _ := hd.s56_eps_conj hgt v
  triv e he := hd.s56_eps_of_comm (hd.L_comm_t (s56_E_le_L d he))
  mem_z v hv := hd.s56_V_sq_eps_mem_of_sq_eq_z h49 hz h1 hv

theorem eq_one_of_fixed (hd : d.Hyp) {w : G} (hw : w ∈ zpowers d.z)
    (hfix : d.s56Y * w * d.s56Y⁻¹ = w) : w = 1 := by
  rcases hd.s56_mem_zpowers_z hw with h | h
  · exact h
  · exfalso
    rw [h] at hfix
    have h2 := (hd.s56_Y_facts).2.2.2.2.2.2
    rw [h2] at hfix
    apply (fiveData hd).ℓ_ne_one
    exact mul_right_cancel (hfix.trans (one_mul d.z).symm)

theorem qq_u_one (hd : d.Hyp) {a : G → G} (tw : Twist d a) {u : G} (huV : u ∈ d.s56V)
    (hfix : d.s56Y * (u * u) * d.s56Y⁻¹ = u * u)
    (ha : a u = 1 ∨ a u = d.pv 10) : qq a u = 1 := by
  refine eq_one_of_fixed hd (tw.qq_mem huV) ?_
  have h10 : d.s56Y * d.pv 10 * d.s56Y⁻¹ = d.pv 10 := by
    have := (hd.s56_Y_facts).2.2.2.2.1
    rw [this]; group
  unfold qq
  rcases ha with h | h
  · rw [h, mul_one, hfix]
  · rw [h]
    calc d.s56Y * (u * u * d.pv 10) * d.s56Y⁻¹
        = (d.s56Y * (u * u) * d.s56Y⁻¹) * (d.s56Y * d.pv 10 * d.s56Y⁻¹) := by group
      _ = u * u * d.pv 10 := by rw [hfix, h10]

theorem comm_of_sq_eq_one {V : Subgroup G} (h : ∀ v ∈ V, v * v = 1) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := by
  have hab := h (a * b) (mul_mem ha hb)
  have h1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
  have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have h3 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  rw [h1, mul_inv_rev, h2, h3]

theorem comm_of_inverted {V : Subgroup G} {t : G} (h : ∀ v ∈ V, t * v * t = v⁻¹)
    (ht : t * t = 1) {a b : G} (ha : a ∈ V) (hb : b ∈ V) : a * b = b * a := by
  have h1 := h (a * b) (mul_mem ha hb)
  have h2 : t * (a * b) * t = (t * a * t) * (t * b * t) := by
    calc t * (a * b) * t = t * a * (t * t) * b * t := by rw [ht]; group
      _ = (t * a * t) * (t * b * t) := by group
  rw [h2, h a ha, h b hb, mul_inv_rev] at h1
  have h3 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := h1
  have := congrArg (fun x => x⁻¹) h3
  simpa using this.symm

end Instances

end CFSG.LocalAnalysis.EvenBN.Tits.N.PZ
