module

public import CFSG.ClassicalInvolution.Asc77.AscSCH02

public section

namespace CFSG.ClassicalInvolution.Asc77.SCH

open scoped commutatorElement

variable {E J : Type*} [Group E] [Group J]

theorem central_twist_pow_eq_one {a z x : E} (hz : z ∈ Subgroup.center E)
    (hzx : z = x * (a * x * a⁻¹)⁻¹) (m : ℕ) (hm : a ^ m = 1) : z ^ m = 1 := by
  have hstep : ∀ n : ℕ, a ^ n * z * (a ^ n)⁻¹ = z := fun n => by
    have := Subgroup.mem_center_iff.1 hz (a ^ n)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have key : ∀ n : ℕ, z ^ n = x * (a ^ n * x * (a ^ n)⁻¹)⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 : a ^ n * (x * (a * x * a⁻¹)⁻¹) * (a ^ n)⁻¹ = z := by rw [← hzx]; exact hstep n
      calc z ^ (n + 1) = z ^ n * z := pow_succ z n
        _ = x * (a ^ n * x * (a ^ n)⁻¹)⁻¹ * (a ^ n * (x * (a * x * a⁻¹)⁻¹) * (a ^ n)⁻¹) := by
            rw [ih, h1]
        _ = x * (a ^ (n + 1) * x * (a ^ (n + 1))⁻¹)⁻¹ := by
            rw [pow_succ]
            group
  rw [key m, hm]
  group

theorem ker_eq_bot_of_unipotent {p : ℕ} [Fact p.Prime] [Finite E] [Group.IsPerfect E]
    (π : E →* J) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (hCp : IsPGroup p π.ker) (R V : Subgroup J)
    (hVR : V ≤ Subgroup.normalizer (R : Set J))
    (hRab : ∀ x ∈ R.comap π, ∀ y ∈ R.comap π, x * y = y * x)
    (hVab : ∀ x ∈ V.comap π, ∀ y ∈ V.comap π, x * y = y * x)
    (a : E) (ha : Nat.Coprime (orderOf a) p)
    (haR : π a ∈ Subgroup.normalizer (R : Set J))
    (haV : ∀ v ∈ V, π a * v * (π a)⁻¹ = v)
    (hfix : ∀ r ∈ R, π a * r * (π a)⁻¹ = r → r = 1)
    (hord : (Nat.card J).factorization p ≤ (Nat.card ↥(R ⊔ V)).factorization p) :
    π.ker = ⊥ := by
  classical
  have hJ : Finite J := Finite.of_surjective π hπ
  set Rt : Subgroup E := R.comap π with hRt
  set Vt : Subgroup E := V.comap π with hVt
  set Pt : Subgroup E := (R ⊔ V).comap π with hPt
  have hRP : Rt ≤ Pt := Subgroup.comap_mono le_sup_left
  have hVP : Vt ≤ Pt := Subgroup.comap_mono le_sup_right
  have hker : π.ker ≤ ⁅Pt, Pt⁆ :=
    ker_le_comm_sub π hC hCp Pt (factorization_comap_ge π hπ _ hord)
  have hkerR : π.ker ≤ Rt := fun x hx => by
    rw [hRt, Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact R.one_mem
  have haRt : ∀ x ∈ Rt, a * x * a⁻¹ ∈ Rt := by
    intro x hx
    rw [hRt, Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 haR (π x)).1 hx
  have haRt' : ∀ x ∈ Rt, a⁻¹ * x * a ∈ Rt := by
    intro x hx
    rw [hRt, Subgroup.mem_comap] at hx ⊢
    simp only [map_mul, map_inv]
    refine (Subgroup.mem_normalizer_iff.1 haR ((π a)⁻¹ * π x * π a)).2 ?_
    rw [show π a * ((π a)⁻¹ * π x * π a) * (π a)⁻¹ = π x by group]
    exact hx
  let R0 : Subgroup E := twistRange Rt hRab a haRt
  have hR0mem : ∀ x, x ∈ R0 ↔ ∃ y ∈ Rt, x = y * (a * y * a⁻¹)⁻¹ := fun x => Iff.rfl
  have hR0R : R0 ≤ Rt := twistRange_le
  have hR0ker : ∀ z ∈ R0, z ∈ π.ker → z = 1 := by
    intro z hzR hzk
    obtain ⟨x, -, hx⟩ := (hR0mem z).1 hzR
    have h1 : z ^ orderOf a = 1 :=
      central_twist_pow_eq_one (hC hzk) hx (orderOf a) (pow_orderOf_eq_one a)
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.1 hCp) ⟨z, hzk⟩
    rw [Subgroup.orderOf_mk] at hn
    have h2 : orderOf z ∣ orderOf a := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf z = 1 := by
      have hdvd : p ^ n ∣ orderOf a := hn ▸ h2
      exact hn.trans (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n ha.symm) hdvd)
    exact orderOf_eq_one_iff.1 h3
  have hRcomm : ∀ r ∈ R, ∀ s ∈ R, r * s = s * r := by
    intro r hr s hs
    have h1 : Function.surjInv hπ r ∈ Rt := by
      rw [hRt, Subgroup.mem_comap, Function.surjInv_eq hπ]; exact hr
    have h2 : Function.surjInv hπ s ∈ Rt := by
      rw [hRt, Subgroup.mem_comap, Function.surjInv_eq hπ]; exact hs
    have := congrArg π (hRab _ h1 _ h2)
    rwa [map_mul, map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ] at this
  let a₀ : J := π a
  have hconj : ∀ r ∈ R, a₀ * r * a₀⁻¹ ∈ R := fun r hr => (Subgroup.mem_normalizer_iff.1 haR r).1 hr
  let θ : R →* R := MonoidHom.mk'
    (fun r => ⟨(r : J) * (a₀ * (r : J) * a₀⁻¹)⁻¹, R.mul_mem r.2 (R.inv_mem (hconj r r.2))⟩)
    (fun r s => by
      apply Subtype.ext
      have hc := hRcomm _ (R.inv_mem (hconj r r.2)) _
        (R.mul_mem s.2 (R.inv_mem (hconj s s.2)))
      show (r : J) * s * (a₀ * ((r : J) * s) * a₀⁻¹)⁻¹ =
        (r : J) * (a₀ * (r : J) * a₀⁻¹)⁻¹ * ((s : J) * (a₀ * (s : J) * a₀⁻¹)⁻¹)
      calc (r : J) * s * (a₀ * ((r : J) * s) * a₀⁻¹)⁻¹
          = (r : J) * ((s : J) * (a₀ * (s : J) * a₀⁻¹)⁻¹ * (a₀ * (r : J) * a₀⁻¹)⁻¹) := by group
        _ = (r : J) * ((a₀ * (r : J) * a₀⁻¹)⁻¹ * ((s : J) * (a₀ * (s : J) * a₀⁻¹)⁻¹)) := by
          rw [← hc]
        _ = _ := by group)
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have h1 : (r : J) * (a₀ * (r : J) * a₀⁻¹)⁻¹ = 1 := congrArg Subtype.val hr
    have h2 : a₀ * (r : J) * a₀⁻¹ = r := by
      have := mul_inv_eq_one.1 h1
      exact this.symm
    exact Subtype.ext (hfix r r.2 h2)
  have hθsurj : Function.Surjective θ := Finite.surjective_of_injective hθinj
  have hRt_ker : ∀ x ∈ Rt, ∃ ρ ∈ R0, π ρ = π x := by
    intro x hx
    obtain ⟨r', hr'⟩ := hθsurj ⟨π x, (Subgroup.mem_comap.1 hx)⟩
    have hr'mem : Function.surjInv hπ (r' : J) ∈ Rt := by
      rw [hRt, Subgroup.mem_comap, Function.surjInv_eq hπ]; exact r'.2
    refine ⟨Function.surjInv hπ (r' : J) *
      (a * Function.surjInv hπ (r' : J) * a⁻¹)⁻¹, ⟨_, hr'mem, rfl⟩, ?_⟩
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Function.surjInv_eq hπ]
    exact congrArg Subtype.val hr'
  have hPR : ∀ g ∈ Pt, π g ∈ Subgroup.normalizer (R : Set J) := by
    intro g hg
    have : R ⊔ V ≤ Subgroup.normalizer (R : Set J) := sup_le Subgroup.le_normalizer hVR
    exact this (Subgroup.mem_comap.1 hg)
  have hPRt : ∀ g ∈ Pt, ∀ y ∈ Rt, g * y * g⁻¹ ∈ Rt := by
    intro g hg y hy
    rw [hRt, Subgroup.mem_comap] at hy ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hPR g hg) (π y)).1 hy
  have hPe : ∀ g ∈ Pt, g * a * g⁻¹ * a⁻¹ ∈ Rt := by
    intro g hg
    have hg' : π g ∈ ((R ⊔ V : Subgroup J) : Set J) := Subgroup.mem_comap.1 hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R V hVR] at hg'
    obtain ⟨r, hr, v, hv, hrv⟩ := hg'
    rw [hRt, Subgroup.mem_comap]
    simp only [map_mul, map_inv]
    rw [← hrv]
    have hva : v * π a * v⁻¹ = π a := by
      have := haV v hv
      rw [mul_inv_eq_iff_eq_mul] at this
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have e1 : r * v * π a * (r * v)⁻¹ * (π a)⁻¹ = r * (v * π a * v⁻¹) * r⁻¹ * (π a)⁻¹ := by group
    rw [e1, hva]
    have : r * π a * r⁻¹ * (π a)⁻¹ = r * (π a * r⁻¹ * (π a)⁻¹) := by group
    rw [this]
    exact R.mul_mem hr ((Subgroup.mem_normalizer_iff.1 haR r⁻¹).1 (R.inv_mem hr))
  have hR0conj : ∀ g ∈ Pt, ∀ m ∈ R0, g * m * g⁻¹ ∈ R0 := by
    intro g hg m hm
    obtain ⟨y, hy, rfl⟩ := (hR0mem m).1 hm
    have hy' := hPRt g hg y hy
    have he := hPe g hg
    refine ⟨g * y * g⁻¹, hy', ?_⟩
    have hcomm := hRab _ he _ (haRt _ hy')
    have h1 : g * (a * y * a⁻¹) * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * (a * (g * y * g⁻¹) * a⁻¹) *
        (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
    have h2 : (g * a * g⁻¹ * a⁻¹) * (a * (g * y * g⁻¹) * a⁻¹) *
        (g * a * g⁻¹ * a⁻¹)⁻¹ = a * (g * y * g⁻¹) * a⁻¹ := by
      rw [hcomm]; group
    calc g * (y * (a * y * a⁻¹)⁻¹) * g⁻¹
        = g * y * g⁻¹ * (g * (a * y * a⁻¹) * g⁻¹)⁻¹ := by group
      _ = g * y * g⁻¹ * (a * (g * y * g⁻¹) * a⁻¹)⁻¹ := by rw [h1, h2]
  have hR0P : R0 ≤ Pt := hR0R.trans hRP
  have hNn : (R0.subgroupOf Pt).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hR0P).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨hR0conj g hg m, fun hm => ?_⟩
    have := hR0conj g⁻¹ (Pt.inv_mem hg) _ hm
    rwa [show g⁻¹ * (g * m * g⁻¹) * g⁻¹⁻¹ = m by group] at this
  let q : Pt →* Pt ⧸ R0.subgroupOf Pt := QuotientGroup.mk' _
  have hdec : ∀ x : Pt, ∃ (z : E) (hz : z ∈ π.ker) (v : E) (hv : v ∈ Vt),
      q x = q ⟨z, hRP (hkerR hz)⟩ * q ⟨v, hVP hv⟩ := by
    intro x
    have hx' : π x ∈ ((R ⊔ V : Subgroup J) : Set J) := Subgroup.mem_comap.1 x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R V hVR] at hx'
    obtain ⟨r, hr, w, hw, hrw⟩ := hx'
    set vh : E := Function.surjInv hπ w with hvh
    have hπvh : π vh = w := Function.surjInv_eq hπ w
    have hvhV : vh ∈ Vt := by rw [hVt, Subgroup.mem_comap, hπvh]; exact hw
    have hrt : (x : E) * vh⁻¹ ∈ Rt := by
      rw [hRt, Subgroup.mem_comap, map_mul, map_inv, hπvh, ← hrw, mul_inv_cancel_right]
      exact hr
    obtain ⟨ρ, hρ, hπρ⟩ := hRt_ker _ hrt
    have hzk : (x : E) * vh⁻¹ * ρ⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hπρ, mul_inv_cancel]
    refine ⟨_, hzk, vh, hvhV, ?_⟩
    have h1 : x = ⟨(x : E) * vh⁻¹ * ρ⁻¹, hRP (hkerR hzk)⟩ * ⟨ρ, hR0P hρ⟩ * ⟨vh, hVP hvhV⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    have h2 : q ⟨ρ, hR0P hρ⟩ = 1 := (QuotientGroup.eq_one_iff _).2 hρ
    conv_lhs => rw [h1]
    rw [map_mul, map_mul, h2, mul_one]
  have hcentral : ∀ (z : E) (hz : z ∈ π.ker) (y : Pt),
      q ⟨z, hRP (hkerR hz)⟩ * q y = q y * q ⟨z, hRP (hkerR hz)⟩ := by
    intro z hz y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hC hz) y).symm
  have hcomm : ∀ x y : Pt, q x * q y = q y * q x := by
    intro x y
    obtain ⟨z₁, hz₁, v₁, hv₁, hx⟩ := hdec x
    obtain ⟨z₂, hz₂, v₂, hv₂, hy⟩ := hdec y
    have hV12 : Commute (q ⟨v₁, hVP hv₁⟩) (q ⟨v₂, hVP hv₂⟩) := by
      show q ⟨v₁, hVP hv₁⟩ * q ⟨v₂, hVP hv₂⟩ = q ⟨v₂, hVP hv₂⟩ * q ⟨v₁, hVP hv₁⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVab v₁ hv₁ v₂ hv₂)
    have h1 : Commute (q ⟨z₁, hRP (hkerR hz₁)⟩ * q ⟨v₁, hVP hv₁⟩)
        (q ⟨z₂, hRP (hkerR hz₂)⟩ * q ⟨v₂, hVP hv₂⟩) :=
      Commute.mul_left
        (Commute.mul_right (hcentral z₁ hz₁ _) (hcentral z₁ hz₁ _))
        (Commute.mul_right (hcentral z₂ hz₂ _).symm hV12)
    rw [hx, hy]
    exact h1.eq
  have hcommP : ⁅Pt, Pt⁆ ≤ R0 := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have hq : q ⁅(⟨g₁, hg₁⟩ : Pt), (⟨g₂, hg₂⟩ : Pt)⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcomm _ _)
    have hmem := (QuotientGroup.eq_one_iff _).1 hq
    rw [Subgroup.mem_subgroupOf] at hmem
    simpa [commutatorElement_def] using hmem
  rw [eq_bot_iff]
  intro z hz
  exact Subgroup.mem_bot.2 (hR0ker z (hcommP (hker hz)) hz)

end CFSG.ClassicalInvolution.Asc77.SCH
