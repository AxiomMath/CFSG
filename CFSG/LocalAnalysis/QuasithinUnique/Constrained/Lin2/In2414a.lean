module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section Cohomology

variable {G : Type*} [Group G]

theorem H3_of_card [Finite G] {N : Subgroup G} {t : G} (htt : t * t = 1)
    (hτN : ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNsq : ∀ a ∈ N, a * a = 1)
    (hcard : Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
      Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = Nat.card N) :
    ∀ n ∈ N, (t * n * t⁻¹) * n = 1 → ∃ m ∈ N, n = (t * m * t⁻¹) * m⁻¹ := by
  let τ : MulAut G := MulAut.conj t
  have hτ : ∀ g : G, τ g = t * g * t⁻¹ := fun _ => rfl
  have hττ : ∀ g : G, τ (τ g) = g := by
    intro g
    rw [hτ, hτ]
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
    rw [hti]
    calc t * (t * g * t) * t = (t * t) * g * (t * t) := by group
      _ = g := by rw [htt]; group
  let φ : N →* N :=
    { toFun := fun m => ⟨t * m * t⁻¹ * m⁻¹, N.mul_mem (hτN m m.2) (N.inv_mem m.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro a b
        apply Subtype.ext
        have hc : (t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
            (a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹) :=
          hNab _ (N.mul_mem (hτN b b.2) (N.inv_mem b.2)) _ (N.inv_mem a.2)
        change t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹ =
          (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (t * (b : G) * t⁻¹ * (b : G)⁻¹)
        calc t * ((a : G) * b) * t⁻¹ * ((a : G) * b)⁻¹
            = (t * (a : G) * t⁻¹) * ((t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by group
          _ = (t * (a : G) * t⁻¹) * ((a : G)⁻¹ * (t * (b : G) * t⁻¹ * (b : G)⁻¹)) := by rw [hc]
          _ = _ := by group }
  have hφ : ∀ m : N, ((φ m : N) : G) = τ m * (m : G)⁻¹ := fun _ => rfl
  set C : Subgroup G := N ⊓ Subgroup.centralizer ({t} : Set G) with hC
  set C' : Subgroup N := C.subgroupOf N with hC'
  have hker : φ.ker = C' := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : τ m * (m : G)⁻¹ = 1 := by
        have := congrArg Subtype.val h
        simpa [hφ] using this
      refine ⟨m.2, ?_⟩
      have h2 : τ m = m := mul_inv_eq_one.1 h1
      rw [hτ] at h2
      calc (m : G) * t = t * (m : G) * t⁻¹ * t := by rw [h2]
        _ = t * (m : G) := by group
    · rintro ⟨-, h⟩
      apply Subtype.ext
      rw [hφ]
      have : τ m = m := by rw [hτ, ← h]; group
      rw [this]; simp
  have hrange_le : φ.range ≤ C' := by
    rintro _ ⟨m, rfl⟩
    rw [hC', Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(φ m).2, ?_⟩
    have hx2 : ((φ m : N) : G) * ((φ m : N) : G) = 1 := hNsq _ (φ m).2
    have hxinv : τ ((φ m : N) : G) = ((φ m : N) : G)⁻¹ := by
      rw [hφ, map_mul, map_inv, hττ, mul_inv_rev, inv_inv]
    have hxx : τ ((φ m : N) : G) = ((φ m : N) : G) := by
      rw [hxinv]; exact (eq_inv_of_mul_eq_one_left hx2).symm
    rw [hτ] at hxx
    calc ((φ m : N) : G) * t = (t * ((φ m : N) : G) * t⁻¹) * t := by rw [hxx]
      _ = t * ((φ m : N) : G) := by group
  have hcardk := Subgroup.card_ker_mul_card_of_surjective φ.rangeRestrict_surjective
  rw [MonoidHom.ker_rangeRestrict, hker] at hcardk
  have hC'card : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ N)).toEquiv
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hrcard : Nat.card φ.range = Nat.card C' := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card C' by rw [hC'card]; exact hCpos)
    rw [hcardk, hC'card, hcard]
  have hrange : φ.range = C' := Subgroup.eq_of_le_of_card_ge hrange_le (by rw [hrcard])
  intro n hn hnn
  have hn' : τ n = n⁻¹ := by
    rw [hτ]
    exact (mul_eq_one_iff_eq_inv.1 hnn)
  have hn'' : n⁻¹ = n := (eq_inv_of_mul_eq_one_left (hNsq n hn)).symm
  have hmemC : (⟨n, hn⟩ : N) ∈ C' := by
    rw [hC', Subgroup.mem_subgroupOf, hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    refine ⟨hn, ?_⟩
    have h1 : τ n = n := by rw [hn', hn'']
    rw [hτ] at h1
    calc n * t = (t * n * t⁻¹) * t := by rw [h1]
      _ = t * n := by group
  rw [← hrange] at hmemC
  obtain ⟨m, hm⟩ := hmemC
  refine ⟨m, m.2, ?_⟩
  have := congrArg Subtype.val hm
  rw [hφ, hτ] at this
  exact this.symm

theorem card_fixed_of_diag {N A A' : Subgroup G} {t : G} (htt : t * t = 1)
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hA : A ≤ N) (hA' : A' ≤ N)
    (hAA' : ∀ a ∈ A, t * a * t⁻¹ ∈ A') (hA'A : ∀ a ∈ A', t * a * t⁻¹ ∈ A)
    (hsup : N = A ⊔ A') (hinf : A ⊓ A' = ⊥) :
    Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) = Nat.card A := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hττ : ∀ g : G, t * (t * g * t⁻¹) * t⁻¹ = g := by
    intro g
    rw [hti]
    calc t * (t * g * t) * t = (t * t) * g * (t * t) := by group
      _ = g := by rw [htt]; group
  have hmem : ∀ a : A, (a : G) * (t * (a : G) * t⁻¹) ∈
      (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    intro a
    refine ⟨N.mul_mem (hA a.2) (hA' (hAA' a a.2)), Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hc := hNab (a : G) (hA a.2) (t * (a : G) * t⁻¹) (hA' (hAA' a a.2))
    have h1 : t * ((a : G) * (t * (a : G) * t⁻¹)) * t⁻¹ = (a : G) * (t * (a : G) * t⁻¹) := by
      calc t * ((a : G) * (t * (a : G) * t⁻¹)) * t⁻¹
          = (t * (a : G) * t⁻¹) * (t * (t * (a : G) * t⁻¹) * t⁻¹) := by group
        _ = (t * (a : G) * t⁻¹) * (a : G) := by rw [hττ]
        _ = (a : G) * (t * (a : G) * t⁻¹) := hc.symm
    calc (a : G) * (t * (a : G) * t⁻¹) * t = (t * ((a : G) * (t * (a : G) * t⁻¹)) * t⁻¹) * t := by
          rw [h1]
      _ = t * ((a : G) * (t * (a : G) * t⁻¹)) := by group
  let f : A → (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :=
    fun a => ⟨(a : G) * (t * (a : G) * t⁻¹), hmem a⟩
  have hf_inj : Function.Injective f := by
    intro a a' h
    have h1 : (a : G) * (t * (a : G) * t⁻¹) = (a' : G) * (t * (a' : G) * t⁻¹) :=
      congrArg Subtype.val h
    have h2 : (a' : G)⁻¹ * (a : G) = t * ((a' : G) * (a : G)⁻¹) * t⁻¹ := by
      calc (a' : G)⁻¹ * (a : G)
          = (a' : G)⁻¹ * ((a : G) * (t * (a : G) * t⁻¹)) * (t * (a : G) * t⁻¹)⁻¹ := by group
        _ = (a' : G)⁻¹ * ((a' : G) * (t * (a' : G) * t⁻¹)) * (t * (a : G) * t⁻¹)⁻¹ := by rw [h1]
        _ = _ := by group
    have h3 : (a' : G)⁻¹ * (a : G) ∈ A ⊓ A' := by
      refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
      rw [h2]
      exact hAA' _ (A.mul_mem a'.2 (A.inv_mem a.2))
    rw [hinf, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, hxN, hxc⟩
    have hxc' := Subgroup.mem_centralizer_singleton_iff.1 hxc
    have hxt : t * x * t⁻¹ = x := by rw [← hxc']; group
    have hx' : x ∈ A ⊔ A' := hsup ▸ hxN
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := A) (H := A')
      (le_normalizer_of_commute fun a ha b hb => hNab a (hA ha) b (hA' hb))).1 hx'
    set b' := t * b * t⁻¹ with hb'
    have hb'A : b' ∈ A := hA'A b hb
    have hbb : b = t * b' * t⁻¹ := by rw [hb', hττ]
    have hb'N : b' ∈ N := hA hb'A
    have h1 : (t * a * t⁻¹) * b' = a * b := by
      have : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
      rw [this] at hxt
      exact hxt
    have h2 : t * (a * b'⁻¹) * t⁻¹ = a * b'⁻¹ := by
      have hτb' : t * b'⁻¹ * t⁻¹ = b⁻¹ := by
        rw [hbb]; group
      calc t * (a * b'⁻¹) * t⁻¹ = (t * a * t⁻¹) * (t * b'⁻¹ * t⁻¹) := by group
        _ = (t * a * t⁻¹) * b⁻¹ := by rw [hτb']
        _ = ((t * a * t⁻¹) * b') * (b'⁻¹ * b⁻¹) := by group
        _ = (a * b) * (b'⁻¹ * b⁻¹) := by rw [h1]
        _ = a * (b * b'⁻¹) * b⁻¹ := by group
        _ = a * (b'⁻¹ * b) * b⁻¹ := by
            rw [hNab b (hA' hb) b'⁻¹ (N.inv_mem hb'N)]
        _ = a * b'⁻¹ := by group
    have h3 : a * b'⁻¹ ∈ A ⊓ A' := by
      refine ⟨A.mul_mem ha (A.inv_mem hb'A), ?_⟩
      have := hAA' _ (A.mul_mem ha (A.inv_mem hb'A))
      rwa [h2] at this
    rw [hinf, Subgroup.mem_bot] at h3
    have hab : a = b' := mul_inv_eq_one.1 h3
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    change a * (t * a * t⁻¹) = a * b
    rw [hbb, ← hab]
  have hbij : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm

end Cohomology

section Swap

variable {G : Type*} [Group G]

structure SwapData (R U V N : Subgroup G) (t : G) : Prop where
  tt : t * t = 1
  R_eq : R = U ⊔ V
  U_norm : R ≤ Subgroup.normalizer (U : Set G)
  V_norm : R ≤ Subgroup.normalizer (V : Set G)
  inf_eq : U ⊓ V = N
  U_ab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  V_ab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a
  U_sq : ∀ a ∈ U, a * a = 1
  V_sq : ∀ a ∈ V, a * a = 1
  tU : ∀ u ∈ U, t * u * t⁻¹ ∈ V
  tV : ∀ v ∈ V, t * v * t⁻¹ ∈ U
  N_cen : ∀ n ∈ N, ∀ r ∈ R, n * r = r * n
  inv_mem_UV : ∀ x ∈ R, x * x = 1 → x ∈ U ∨ x ∈ V

namespace SwapData

variable {R U V N : Subgroup G} {t : G} (hs : SwapData R U V N t)
include hs

theorem U_le : U ≤ R := hs.R_eq ▸ le_sup_left

theorem V_le : V ≤ R := hs.R_eq ▸ le_sup_right

theorem N_le_U : N ≤ U := hs.inf_eq ▸ inf_le_left

theorem N_le_V : N ≤ V := hs.inf_eq ▸ inf_le_right

theorem N_le_R : N ≤ R := hs.N_le_U.trans hs.U_le

theorem tt_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right hs.tt

theorem tau_tau (x : G) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have h := hs.tt_inv
  rw [h]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [hs.tt]; group

theorem comm_mem {u v : G} (hu : u ∈ U) (hv : v ∈ V) : u * v * u⁻¹ * v⁻¹ ∈ N := by
  rw [← hs.inf_eq]
  constructor
  · have h1 : v * u⁻¹ * v⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (hs.U_norm (hs.V_le hv)) u⁻¹).1 (U.inv_mem hu)
    have := U.mul_mem hu h1
    simpa [mul_assoc] using this
  · have h1 : u * v * u⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hs.V_norm (hs.U_le hu)) v).1 hv
    exact V.mul_mem h1 (V.inv_mem hv)

theorem tau_N {n : G} (hn : n ∈ N) : t * n * t⁻¹ ∈ N := by
  rw [← hs.inf_eq] at hn ⊢
  exact ⟨hs.tV n hn.2, hs.tU n hn.1⟩

theorem tau_R {r : G} (hr : r ∈ R) : t * r * t⁻¹ ∈ R := by
  have hr' : r ∈ U ⊔ V := hs.R_eq ▸ hr
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := U) (H := V)
    (fun x hx => hs.U_norm (hs.V_le hx))).1 hr'
  have : t * (u * v) * t⁻¹ = (t * u * t⁻¹) * (t * v * t⁻¹) := by group
  rw [this]
  exact R.mul_mem (hs.V_le (hs.tU u hu)) (hs.U_le (hs.tV v hv))

theorem fixed_V {x : G} (hx : x ∈ V) (hc : t * x = x * t) : x ∈ N := by
  rw [← hs.inf_eq]
  refine ⟨?_, hx⟩
  have h := hs.tV x hx
  rwa [show t * x * t⁻¹ = x by rw [hc]; group] at h

theorem fixed_U {x : G} (hx : x ∈ U) (hc : t * x = x * t) : x ∈ N := by
  rw [← hs.inf_eq]
  refine ⟨hx, ?_⟩
  have h := hs.tU x hx
  rwa [show t * x * t⁻¹ = x by rw [hc]; group] at h

theorem mem_N_of_inv {x : G} (hx : x ∈ R) (hx2 : x * x = 1) (hτ : (t * x * t⁻¹) * x⁻¹ ∈ N) :
    x ∈ N := by
  rcases hs.inv_mem_UV x hx hx2 with hU | hV
  · have h1 : t * x * t⁻¹ ∈ U := by
      have : t * x * t⁻¹ = ((t * x * t⁻¹) * x⁻¹) * x := by group
      rw [this]
      exact U.mul_mem (hs.N_le_U hτ) hU
    have h2 : t * x * t⁻¹ ∈ N := by rw [← hs.inf_eq]; exact ⟨h1, hs.tU x hU⟩
    have := hs.tau_N h2
    rwa [hs.tau_tau] at this
  · have h1 : t * x * t⁻¹ ∈ V := by
      have : t * x * t⁻¹ = ((t * x * t⁻¹) * x⁻¹) * x := by group
      rw [this]
      exact V.mul_mem (hs.N_le_V hτ) hV
    have h2 : t * x * t⁻¹ ∈ N := by rw [← hs.inf_eq]; exact ⟨hs.tV x hV, h1⟩
    have := hs.tau_N h2
    rwa [hs.tau_tau] at this

theorem sq_mem_N {r : G} (hr : r ∈ R) : r * r ∈ N := by
  have hr' : r ∈ U ⊔ V := hs.R_eq ▸ hr
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := U) (H := V)
    (fun x hx => hs.U_norm (hs.V_le hx))).1 hr'
  set ν := u * v * u⁻¹ * v⁻¹ with hν
  have hνN : ν ∈ N := hs.comm_mem hu hv
  have e : (u * v) * (u * v) = ν⁻¹ * (u * u) * (v * v) := by
    have h1 : v * u = ν⁻¹ * u * v := by rw [hν]; group
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (ν⁻¹ * u * v) * v := by rw [h1]
      _ = u * ν⁻¹ * u * v * v := by group
      _ = ν⁻¹ * u * u * v * v := by
          have hc : u * ν⁻¹ = ν⁻¹ * u := by
            have := hs.N_cen ν⁻¹ (N.inv_mem hνN) u (hs.U_le hu)
            exact this.symm
          rw [hc]
      _ = ν⁻¹ * (u * u) * (v * v) := by group
  rw [e, hs.U_sq u hu, hs.V_sq v hv]
  simpa using N.inv_mem hνN

theorem H2 : ∀ r ∈ R, (t * r * t⁻¹) * r ∈ N → ∃ s ∈ R, r * (t * s * t⁻¹ * s⁻¹)⁻¹ ∈ N := by
  intro r hr hN
  have hr' : r ∈ U ⊔ V := hs.R_eq ▸ hr
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := U) (H := V)
    (fun x hx => hs.U_norm (hs.V_le hx))).1 hr'
  set a := t * u * t⁻¹ with ha
  set b := t * v * t⁻¹ with hb
  have haV : a ∈ V := hs.tU u hu
  have hbU : b ∈ U := hs.tV v hv
  have hτ : t * (u * v) * t⁻¹ = a * b := by rw [ha, hb]; group
  rw [hτ] at hN
  have hbu : b * u ∈ U := U.mul_mem hbU hu
  have hc := hs.comm_mem hbu haV
  have hNm : (b * u) * (a * v) ∈ N := by
    have e : (b * u) * (a * v) = ((b * u) * a * (b * u)⁻¹ * a⁻¹) * (a * b * (u * v)) := by group
    rw [e]
    exact N.mul_mem hc (by simpa [mul_assoc] using hN)
  have hbuN : b * u ∈ N := by
    rw [← hs.inf_eq]
    refine ⟨hbu, ?_⟩
    have : b * u = ((b * u) * (a * v)) * (a * v)⁻¹ := by group
    rw [this]
    exact V.mul_mem (hs.N_le_V hNm) (V.inv_mem (V.mul_mem haV hv))
  refine ⟨v⁻¹, R.inv_mem (hs.V_le hv), ?_⟩
  have e : u * v * (t * v⁻¹ * t⁻¹ * (v⁻¹)⁻¹)⁻¹ = u * b := by
    rw [hb]; group
  rw [e]
  have : u * b = b * u := hs.U_ab u hu b hbU
  rw [this]
  exact hbuN

theorem exists_coboundary
    (H3 : ∀ n ∈ N, (t * n * t⁻¹) * n = 1 → ∃ m ∈ N, n = (t * m * t⁻¹) * m⁻¹)
    {r : G} (hr : r ∈ R) (hinv : (t * r * t⁻¹) * r = 1) :
    ∃ s ∈ R, r = (t * s * t⁻¹) * s⁻¹ := by
  obtain ⟨s, hsR, hn⟩ := hs.H2 r hr (by rw [hinv]; exact N.one_mem)
  set n := r * (t * s * t⁻¹ * s⁻¹)⁻¹ with hndef
  have hr_eq : r = n * (t * s * t⁻¹ * s⁻¹) := by rw [hndef]; group
  have hτs : t * s * t⁻¹ ∈ R := hs.tau_R hsR
  have hX : t * s * t⁻¹ * s⁻¹ ∈ R := R.mul_mem hτs (R.inv_mem hsR)
  have hτn : t * n * t⁻¹ ∈ N := hs.tau_N hn
  have hτn1 : (t * n * t⁻¹) * n = 1 := by
    have h1 : t * r * t⁻¹ = (t * n * t⁻¹) * (s * (t * s * t⁻¹)⁻¹) := by
      rw [hr_eq]
      have := hs.tau_tau s
      calc t * (n * (t * s * t⁻¹ * s⁻¹)) * t⁻¹
          = (t * n * t⁻¹) * ((t * (t * s * t⁻¹) * t⁻¹) * (t * s⁻¹ * t⁻¹)) := by group
        _ = (t * n * t⁻¹) * (s * (t * s * t⁻¹)⁻¹) := by rw [this]; group
    have hc2 : n * (t * s * t⁻¹ * s⁻¹) = (t * s * t⁻¹ * s⁻¹) * n := hs.N_cen n hn _ hX
    rw [h1, hr_eq] at hinv
    calc (t * n * t⁻¹) * n = (t * n * t⁻¹) * ((s * (t * s * t⁻¹)⁻¹) * (t * s * t⁻¹ * s⁻¹)) * n := by
          group
      _ = ((t * n * t⁻¹) * (s * (t * s * t⁻¹)⁻¹)) * ((t * s * t⁻¹ * s⁻¹) * n) := by group
      _ = ((t * n * t⁻¹) * (s * (t * s * t⁻¹)⁻¹)) * (n * (t * s * t⁻¹ * s⁻¹)) := by rw [hc2]
      _ = 1 := hinv
  obtain ⟨m, hm, hnm⟩ := H3 n hn hτn1
  refine ⟨m * s, R.mul_mem (hs.N_le_R hm) hsR, ?_⟩
  have hcm : m⁻¹ * (t * s * t⁻¹) = (t * s * t⁻¹) * m⁻¹ := hs.N_cen m⁻¹ (N.inv_mem hm) _ hτs
  rw [hr_eq, hnm]
  calc t * m * t⁻¹ * m⁻¹ * (t * s * t⁻¹ * s⁻¹)
      = (t * m * t⁻¹) * (m⁻¹ * (t * s * t⁻¹)) * s⁻¹ := by group
    _ = (t * m * t⁻¹) * ((t * s * t⁻¹) * m⁻¹) * s⁻¹ := by rw [hcm]
    _ = t * (m * s) * t⁻¹ * (m * s)⁻¹ := by
        have hcm2 : m⁻¹ * s⁻¹ = s⁻¹ * m⁻¹ := hs.N_cen m⁻¹ (N.inv_mem hm) _ (R.inv_mem hsR)
        calc (t * m * t⁻¹) * ((t * s * t⁻¹) * m⁻¹) * s⁻¹
            = (t * m * t⁻¹) * (t * s * t⁻¹) * (m⁻¹ * s⁻¹) := by group
          _ = (t * m * t⁻¹) * (t * s * t⁻¹) * (s⁻¹ * m⁻¹) := by rw [hcm2]
          _ = t * (m * s) * t⁻¹ * (m * s)⁻¹ := by group

theorem transitive_of_H3
    (H3 : ∀ n ∈ N, (t * n * t⁻¹) * n = 1 → ∃ m ∈ N, n = (t * m * t⁻¹) * m⁻¹)
    {i : G} (hi : t⁻¹ * i ∈ R) (hi2 : i * i = 1) : ∃ s ∈ R, i = s * t * s⁻¹ := by
  have hti := hs.tt_inv
  have hr : t * i ∈ R := by rw [← hti]; exact hi
  have hinv : (t * (t * i) * t⁻¹) * (t * i) = 1 := by
    rw [hti]
    calc t * (t * i) * t * (t * i) = (t * t) * (i * (t * t) * i) := by group
      _ = 1 := by rw [hs.tt]; simpa using hi2
  obtain ⟨s, hsR, hs'⟩ := hs.exists_coboundary H3 hr hinv
  refine ⟨s, hsR, ?_⟩
  calc i = t * (t * i) := by rw [← mul_assoc, hs.tt, one_mul]
    _ = t * (t * s * t⁻¹ * s⁻¹) := by rw [hs']
    _ = (t * t) * s * t⁻¹ * s⁻¹ := by group
    _ = s * t⁻¹ * s⁻¹ := by rw [hs.tt, one_mul]
    _ = s * t * s⁻¹ := by rw [hti]

@[expose] def Rt : Subgroup G where
  carrier := {r | r ∈ R ∧ (t * r * t⁻¹) * r⁻¹ ∈ N}
  one_mem' := ⟨R.one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨haR, ha⟩ ⟨hbR, hb⟩
    refine ⟨R.mul_mem haR hbR, ?_⟩
    have hc : (a * ((t * b * t⁻¹) * b⁻¹) * a⁻¹) = (t * b * t⁻¹) * b⁻¹ := by
      have := hs.N_cen _ hb a haR
      calc a * ((t * b * t⁻¹) * b⁻¹) * a⁻¹ = (a * ((t * b * t⁻¹) * b⁻¹)) * a⁻¹ := by group
        _ = (((t * b * t⁻¹) * b⁻¹) * a) * a⁻¹ := by rw [← this]
        _ = (t * b * t⁻¹) * b⁻¹ := by group
    have e : t * (a * b) * t⁻¹ * (a * b)⁻¹ =
        ((t * a * t⁻¹) * a⁻¹) * (a * ((t * b * t⁻¹) * b⁻¹) * a⁻¹) := by group
    rw [e, hc]
    exact N.mul_mem ha hb
  inv_mem' := by
    rintro a ⟨haR, ha⟩
    refine ⟨R.inv_mem haR, ?_⟩
    have hc : a⁻¹ * ((t * a * t⁻¹) * a⁻¹) * a = (t * a * t⁻¹) * a⁻¹ := by
      have := hs.N_cen _ ha a⁻¹ (R.inv_mem haR)
      calc a⁻¹ * ((t * a * t⁻¹) * a⁻¹) * a = (a⁻¹ * ((t * a * t⁻¹) * a⁻¹)) * a := by group
        _ = (((t * a * t⁻¹) * a⁻¹) * a⁻¹) * a := by rw [← this]
        _ = (t * a * t⁻¹) * a⁻¹ := by group
    have e : t * a⁻¹ * t⁻¹ * (a⁻¹)⁻¹ = (a⁻¹ * ((t * a * t⁻¹) * a⁻¹) * a)⁻¹ := by group
    rw [e, hc]
    exact N.inv_mem ha

theorem Rt_le : hs.Rt ≤ R := fun _ h => h.1

theorem N_le_Rt : N ≤ hs.Rt := fun _ hn =>
  ⟨hs.N_le_R hn, N.mul_mem (hs.tau_N hn) (N.inv_mem hn)⟩

theorem Rt_inf_V : hs.Rt ⊓ V = N := by
  apply le_antisymm
  · rintro x ⟨⟨hxR, hx⟩, hxV⟩
    have h1 : t * x * t⁻¹ ∈ V := by
      have : t * x * t⁻¹ = ((t * x * t⁻¹) * x⁻¹) * x := by group
      rw [this]
      exact V.mul_mem (hs.N_le_V hx) hxV
    have h2 : t * x * t⁻¹ ∈ N := by rw [← hs.inf_eq]; exact ⟨hs.tV x hxV, h1⟩
    have := hs.tau_N h2
    rwa [hs.tau_tau] at this
  · intro n hn
    exact ⟨hs.N_le_Rt hn, hs.N_le_V hn⟩

theorem R_le_Rt_sup_V : R ≤ hs.Rt ⊔ V := by
  intro r hr
  have hr' : r ∈ U ⊔ V := hs.R_eq ▸ hr
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := U) (H := V)
    (fun x hx => hs.U_norm (hs.V_le hx))).1 hr'
  set c₀ := u * (t * u * t⁻¹) with hc₀
  have hτu : t * u * t⁻¹ ∈ V := hs.tU u hu
  have hc₀R : c₀ ∈ R := R.mul_mem (hs.U_le hu) (hs.V_le hτu)
  have hfix : (t * c₀ * t⁻¹) * c₀⁻¹ ∈ N := by
    have e : (t * c₀ * t⁻¹) * c₀⁻¹ = ((t * u * t⁻¹) * u * (t * u * t⁻¹)⁻¹ * u⁻¹) := by
      rw [hc₀]
      have := hs.tau_tau u
      calc t * (u * (t * u * t⁻¹)) * t⁻¹ * (u * (t * u * t⁻¹))⁻¹
          = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) * (t * u * t⁻¹)⁻¹ * u⁻¹ := by group
        _ = (t * u * t⁻¹) * u * (t * u * t⁻¹)⁻¹ * u⁻¹ := by rw [this]
    rw [e]
    have := hs.comm_mem hu hτu
    have h2 : ((t * u * t⁻¹) * u * (t * u * t⁻¹)⁻¹ * u⁻¹) =
        (u * (t * u * t⁻¹) * u⁻¹ * (t * u * t⁻¹)⁻¹)⁻¹ := by group
    rw [h2]
    exact N.inv_mem this
  have hc₀t : c₀ ∈ hs.Rt := ⟨hc₀R, hfix⟩
  have hv' : c₀⁻¹ * (u * v) ∈ V := by
    have e : c₀⁻¹ * (u * v) = (t * u * t⁻¹)⁻¹ * v := by rw [hc₀]; group
    rw [e]
    exact V.mul_mem (V.inv_mem hτu) hv
  have e : u * v = c₀ * (c₀⁻¹ * (u * v)) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc₀t) (Subgroup.mem_sup_right hv')

theorem tau_comm {s : G} : t * (t * s * t⁻¹ * s⁻¹) * t⁻¹ = (t * s * t⁻¹ * s⁻¹)⁻¹ := by
  have h1 := hs.tau_tau s
  calc t * (t * s * t⁻¹ * s⁻¹) * t⁻¹ = (t * (t * s * t⁻¹) * t⁻¹) * (t * s⁻¹ * t⁻¹) := by group
    _ = s * (t * s⁻¹ * t⁻¹) := by rw [h1]
    _ = (t * s * t⁻¹ * s⁻¹)⁻¹ := by group

theorem comm_mem_R {s : G} (hsR : s ∈ R) : t * s * t⁻¹ * s⁻¹ ∈ R :=
  R.mul_mem (hs.tau_R hsR) (R.inv_mem hsR)

theorem comm_mem_Rt {s : G} (hsR : s ∈ R) : t * s * t⁻¹ * s⁻¹ ∈ hs.Rt := by
  have hgR : t * s * t⁻¹ * s⁻¹ ∈ R := hs.comm_mem_R hsR
  refine ⟨hgR, ?_⟩
  rw [hs.tau_comm]
  have : ((t * s * t⁻¹ * s⁻¹)⁻¹) * (t * s * t⁻¹ * s⁻¹)⁻¹ =
      ((t * s * t⁻¹ * s⁻¹) * (t * s * t⁻¹ * s⁻¹))⁻¹ := by group
  rw [this]
  exact N.inv_mem (hs.sq_mem_N hgR)

theorem C_eq_N (hτ : ∀ n ∈ N, t * n = n * t) :
    R ⊓ Subgroup.centralizer ({t} : Set G) = N := by
  apply le_antisymm
  · rintro r ⟨hrR, hrc⟩
    have hc : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.1 hrc
    have hτr : t * r * t⁻¹ = r := by rw [← hc]; group
    obtain ⟨s, hsR, hn⟩ := hs.H2 r hrR (by rw [hτr]; exact hs.sq_mem_N hrR)
    set g := t * s * t⁻¹ * s⁻¹ with hg
    set n := r * g⁻¹ with hndef
    have hr_eq : r = n * g := by rw [hndef]; group
    have hgR : g ∈ R := hs.comm_mem_R hsR
    have hτg : t * g * t⁻¹ = g⁻¹ := hs.tau_comm
    have hτn : t * n * t⁻¹ = n := by
      have := hτ n hn
      rw [this]; group
    have hgg : g * g = 1 := by
      have h1 : t * r * t⁻¹ = n * g⁻¹ := by
        rw [hr_eq]
        calc t * (n * g) * t⁻¹ = (t * n * t⁻¹) * (t * g * t⁻¹) := by group
          _ = n * g⁻¹ := by rw [hτn, hτg]
      rw [hτr] at h1
      have h2 : n * g = n * g⁻¹ := by rw [← hr_eq]; exact h1
      have h3 : g = g⁻¹ := mul_left_cancel h2
      calc g * g = g * g⁻¹ := by rw [← h3]
        _ = 1 := by group
    have hgN : g ∈ N := by
      refine hs.mem_N_of_inv hgR hgg ?_
      rw [hτg]
      have : g⁻¹ * g⁻¹ = 1 := by
        calc g⁻¹ * g⁻¹ = (g * g)⁻¹ := by group
          _ = 1 := by rw [hgg]; simp
      rw [this]
      exact N.one_mem
    rw [hr_eq]
    exact N.mul_mem hn hgN
  · intro n hn
    exact ⟨hs.N_le_R hn, Subgroup.mem_centralizer_singleton_iff.2 (hτ n hn).symm⟩

theorem omegaOneOf_C :
    omegaOneOf (R ⊓ Subgroup.centralizer ({t} : Set G)) =
      N ⊓ Subgroup.centralizer ({t} : Set G) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨⟨hxR, hxc⟩, hx2⟩
    have hc : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.1 hxc
    have hx2' : x * x = 1 := by rw [← sq]; exact hx2
    refine ⟨?_, hxc⟩
    rcases hs.inv_mem_UV x hxR hx2' with hU | hV
    · exact hs.fixed_U hU hc.symm
    · exact hs.fixed_V hV hc.symm
  · intro y hy
    apply Subgroup.subset_closure
    refine ⟨⟨hs.N_le_R hy.1, hy.2⟩, ?_⟩
    rw [sq]
    exact hs.U_sq y (hs.N_le_U hy.1)

theorem not_commutator_le {u : G} (hu : u ∈ U) (hun : u ∉ N) :
    ¬ ⁅R, Subgroup.zpowers t⁆ ≤ N := by
  intro hle
  have hmem : ⁅u, t⁆ ∈ ⁅R, Subgroup.zpowers t⁆ :=
    Subgroup.commutator_mem_commutator (hs.U_le hu) (Subgroup.mem_zpowers t)
  have hN : u * t * u⁻¹ * t⁻¹ ∈ N := by
    have := hle hmem
    simpa [commutatorElement_def] using this
  have h1 : t * u⁻¹ * t⁻¹ ∈ U := by
    have e : t * u⁻¹ * t⁻¹ = u⁻¹ * (u * t * u⁻¹ * t⁻¹) := by group
    rw [e]
    exact U.mul_mem (U.inv_mem hu) (hs.N_le_U hN)
  have h2 : t * u * t⁻¹ ∈ U := by
    have := U.inv_mem h1
    simpa [mul_assoc] using this
  have h3 : t * u * t⁻¹ ∈ N := by
    rw [← hs.inf_eq]
    exact ⟨h2, hs.tU u hu⟩
  have h4 := hs.tau_N h3
  rw [hs.tau_tau] at h4
  exact hun h4

section Finite

variable [Finite G]

theorem card_V_eq : Nat.card V = Nat.card U := by
  have h1 : Function.Injective (fun u : U => (⟨t * u * t⁻¹, hs.tU u u.2⟩ : V)) := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only at h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  have h2 : Function.Injective (fun v : V => (⟨t * v * t⁻¹, hs.tV v v.2⟩ : U)) := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only at h
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
  exact le_antisymm (Nat.card_le_card_of_injective _ h2) (Nat.card_le_card_of_injective _ h1)

theorem card_Rt : Nat.card hs.Rt = Nat.card U := by
  have hRV : hs.Rt ≤ Subgroup.normalizer (V : Set G) := hs.Rt_le.trans hs.V_norm
  have h1 := card_sup_mul_card_inf hRV
  have hsup : hs.Rt ⊔ V = R :=
    le_antisymm (sup_le hs.Rt_le hs.V_le) hs.R_le_Rt_sup_V
  rw [hsup, hs.Rt_inf_V] at h1
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hs.U_le.trans hs.V_norm
  have h2 := card_sup_mul_card_inf hUV
  rw [← hs.R_eq, hs.inf_eq] at h2
  have hVpos : 0 < Nat.card V := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hVpos
  rw [← h1, h2]

theorem transitive_of_centralizes (hτ : ∀ n ∈ N, t * n = n * t)
    (hcard : Nat.card U = Nat.card N * Nat.card N) {i : G} (hi : t⁻¹ * i ∈ R)
    (hi2 : i * i = 1) : ∃ s ∈ R, i = s * t * s⁻¹ := by
  classical
  have hti := hs.tt_inv
  set N' : Subgroup R := N.subgroupOf R with hN'
  have hCN := hs.C_eq_N hτ
  let F : R → hs.Rt := fun s => ⟨t * s * t⁻¹ * s⁻¹, hs.comm_mem_Rt s.2⟩
  have hF : ∀ a b : R, F a = F b → (a : R)⁻¹ * b ∈ N' := by
    intro a b hab
    have h1 : t * (a : G) * t⁻¹ * (a : G)⁻¹ = t * (b : G) * t⁻¹ * (b : G)⁻¹ :=
      congrArg Subtype.val hab
    have h0 : t * (a : G) * t⁻¹ = (t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G) := by
      calc t * (a : G) * t⁻¹ = (t * (a : G) * t⁻¹ * (a : G)⁻¹) * (a : G) := by group
        _ = _ := by rw [h1]
    have h2 : t * ((b : G)⁻¹ * (a : G)) * t⁻¹ = (b : G)⁻¹ * (a : G) := by
      calc t * ((b : G)⁻¹ * (a : G)) * t⁻¹
          = (t * (b : G) * t⁻¹)⁻¹ * (t * (a : G) * t⁻¹) := by group
        _ = (t * (b : G) * t⁻¹)⁻¹ * ((t * (b : G) * t⁻¹ * (b : G)⁻¹) * (a : G)) := by rw [h0]
        _ = (b : G)⁻¹ * (a : G) := by group
    have h3 : (b : G)⁻¹ * (a : G) ∈ R ⊓ Subgroup.centralizer ({t} : Set G) := by
      refine ⟨R.mul_mem (R.inv_mem b.2) a.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc (b : G)⁻¹ * (a : G) * t = (t * ((b : G)⁻¹ * (a : G)) * t⁻¹) * t := by rw [h2]
        _ = t * ((b : G)⁻¹ * (a : G)) := by group
    rw [hCN] at h3
    rw [hN', Subgroup.mem_subgroupOf]
    have := N.inv_mem h3
    simpa using this
  have hF' : ∀ a b : R, (a : R)⁻¹ * b ∈ N' → F a = F b := by
    intro a b hab
    rw [hN', Subgroup.mem_subgroupOf] at hab
    have hab' : (a : G)⁻¹ * (b : G) ∈ N := hab
    apply Subtype.ext
    have hb : (b : G) = (a : G) * ((a : G)⁻¹ * (b : G)) := by group
    set c := (a : G)⁻¹ * (b : G) with hc
    have hτc : t * c * t⁻¹ = c := by rw [hτ c hab']; group
    change t * (a : G) * t⁻¹ * (a : G)⁻¹ = t * (b : G) * t⁻¹ * (b : G)⁻¹
    rw [hb]
    calc t * (a : G) * t⁻¹ * (a : G)⁻¹
        = (t * (a : G) * t⁻¹) * c * c⁻¹ * (a : G)⁻¹ := by group
      _ = (t * (a : G) * t⁻¹) * (t * c * t⁻¹) * c⁻¹ * (a : G)⁻¹ := by rw [hτc]
      _ = t * ((a : G) * c) * t⁻¹ * ((a : G) * c)⁻¹ := by group
  let F' : R ⧸ N' → hs.Rt :=
    Quotient.lift F (fun a b hab => hF' a b (QuotientGroup.leftRel_apply.1 hab))
  have hinj : Function.Injective F' := by
    intro q₁ q₂
    induction q₁ using QuotientGroup.induction_on with | H a => ?_
    induction q₂ using QuotientGroup.induction_on with | H b => ?_
    intro h
    exact QuotientGroup.eq.2 (hF a b h)
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hs.N_le_R).toEquiv
  have hRcard : Nat.card R = Nat.card (R ⧸ N') * Nat.card N' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup N'
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hs.U_le.trans hs.V_norm
  have h2 := card_sup_mul_card_inf hUV
  rw [← hs.R_eq, hs.inf_eq, hs.card_V_eq, hcard] at h2
  have hcpos : 0 < Nat.card N := Nat.card_pos
  have hR3 : Nat.card R = Nat.card N * Nat.card N * Nat.card N := by
    apply Nat.eq_of_mul_eq_mul_right hcpos
    rw [h2]; ring
  have hQcard : Nat.card (R ⧸ N') = Nat.card U := by
    apply Nat.eq_of_mul_eq_mul_right hcpos
    rw [← hN'card, ← hRcard, hR3, hN'card, hcard]
  have hbij : Function.Bijective F' :=
    hinj.bijective_of_nat_card_le (by rw [hQcard, hs.card_Rt])
  have hr : t * i ∈ R := by rw [← hti]; exact hi
  have hinv : t * (t * i) * t⁻¹ = (t * i)⁻¹ := by
    have hi' : i⁻¹ = i := (eq_inv_of_mul_eq_one_left hi2).symm
    calc t * (t * i) * t⁻¹ = (t * t) * i * t⁻¹ := by group
      _ = i * t⁻¹ := by rw [hs.tt]; group
      _ = i⁻¹ * t⁻¹ := by rw [hi']
      _ = (t * i)⁻¹ := by group
  have hrRt : t * i ∈ hs.Rt := by
    refine ⟨hr, ?_⟩
    rw [hinv]
    have : (t * i)⁻¹ * (t * i)⁻¹ = ((t * i) * (t * i))⁻¹ := by group
    rw [this]
    exact N.inv_mem (hs.sq_mem_N hr)
  obtain ⟨q, hq⟩ := hbij.2 ⟨t * i, hrRt⟩
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
  have hs' : t * (s : G) * t⁻¹ * (s : G)⁻¹ = t * i := congrArg Subtype.val hq
  refine ⟨s, s.2, ?_⟩
  calc i = t * (t * i) := by rw [← mul_assoc, hs.tt, one_mul]
    _ = t * (t * (s : G) * t⁻¹ * (s : G)⁻¹) := by rw [hs']
    _ = (t * t) * (s : G) * t⁻¹ * (s : G)⁻¹ := by group
    _ = (s : G) * t * (s : G)⁻¹ := by rw [hs.tt, one_mul, hti]

omit [Finite G] in
theorem exists_fixed_lift
    (H3 : ∀ n ∈ N, (t * n * t⁻¹) * n = 1 → ∃ m ∈ N, n = (t * m * t⁻¹) * m⁻¹)
    {r : G} (hr : r ∈ R) (hfix : (t * r * t⁻¹) * r⁻¹ ∈ N) :
    ∃ m ∈ N, t * (r * m) * t⁻¹ = r * m := by
  set n₀ := (t * r * t⁻¹) * r⁻¹ with hn₀
  have hτr : t * r * t⁻¹ = n₀ * r := by rw [hn₀]; group
  have hτn₀ : t * n₀ * t⁻¹ ∈ N := hs.tau_N hfix
  have h1 : (t * n₀ * t⁻¹) * n₀ = 1 := by
    have e : t * (t * r * t⁻¹) * t⁻¹ = r := hs.tau_tau r
    rw [hτr] at e
    have e2 : t * (n₀ * r) * t⁻¹ = (t * n₀ * t⁻¹) * (t * r * t⁻¹) := by group
    rw [e2, hτr] at e
    have hc : n₀ * r = r * n₀ := hs.N_cen n₀ hfix r hr
    calc (t * n₀ * t⁻¹) * n₀ = ((t * n₀ * t⁻¹) * (n₀ * r)) * r⁻¹ := by group
      _ = r * r⁻¹ := by rw [e]
      _ = 1 := by group
  obtain ⟨m, hm, hnm⟩ := H3 n₀ hfix h1
  refine ⟨m⁻¹, N.inv_mem hm, ?_⟩
  have hτm : t * m * t⁻¹ ∈ N := hs.tau_N hm
  have hcen : (t * m * t⁻¹) * (m⁻¹ * r) = (m⁻¹ * r) * (t * m * t⁻¹) :=
    hs.N_cen _ hτm _ (R.mul_mem (R.inv_mem (hs.N_le_R hm)) hr)
  have hcm : m⁻¹ * r = r * m⁻¹ := hs.N_cen m⁻¹ (N.inv_mem hm) r hr
  calc t * (r * m⁻¹) * t⁻¹ = (t * r * t⁻¹) * (t * m * t⁻¹)⁻¹ := by group
    _ = (n₀ * r) * (t * m * t⁻¹)⁻¹ := by rw [hτr]
    _ = ((t * m * t⁻¹) * m⁻¹ * r) * (t * m * t⁻¹)⁻¹ := by rw [hnm]
    _ = (t * m * t⁻¹) * (m⁻¹ * r) * (t * m * t⁻¹)⁻¹ := by group
    _ = (m⁻¹ * r) * (t * m * t⁻¹) * (t * m * t⁻¹)⁻¹ := by rw [hcen]
    _ = r * m⁻¹ := by rw [hcm]; group

omit [Finite G] in
theorem R_le_C_sup_V
    (H3 : ∀ n ∈ N, (t * n * t⁻¹) * n = 1 → ∃ m ∈ N, n = (t * m * t⁻¹) * m⁻¹) :
    R ≤ (R ⊓ Subgroup.centralizer ({t} : Set G)) ⊔ V := by
  intro r hr
  have hr' : r ∈ U ⊔ V := hs.R_eq ▸ hr
  obtain ⟨u, hu, v, hv, rfl⟩ := (mem_sup_iff_of_le_normalizer (N := U) (H := V)
    (fun x hx => hs.U_norm (hs.V_le hx))).1 hr'
  set c₀ := u * (t * u * t⁻¹) with hc₀
  have hτu : t * u * t⁻¹ ∈ V := hs.tU u hu
  have hc₀R : c₀ ∈ R := R.mul_mem (hs.U_le hu) (hs.V_le hτu)
  have hfix : (t * c₀ * t⁻¹) * c₀⁻¹ ∈ N := by
    have e : (t * c₀ * t⁻¹) * c₀⁻¹ = ((t * u * t⁻¹) * u * (t * u * t⁻¹)⁻¹ * u⁻¹) := by
      rw [hc₀]
      have := hs.tau_tau u
      calc t * (u * (t * u * t⁻¹)) * t⁻¹ * (u * (t * u * t⁻¹))⁻¹
          = (t * u * t⁻¹) * (t * (t * u * t⁻¹) * t⁻¹) * (t * u * t⁻¹)⁻¹ * u⁻¹ := by group
        _ = (t * u * t⁻¹) * u * (t * u * t⁻¹)⁻¹ * u⁻¹ := by rw [this]
    rw [e]
    have := hs.comm_mem hu hτu
    have h2 : ((t * u * t⁻¹) * u * (t * u * t⁻¹)⁻¹ * u⁻¹) =
        (u * (t * u * t⁻¹) * u⁻¹ * (t * u * t⁻¹)⁻¹)⁻¹ := by group
    rw [h2]
    exact N.inv_mem this
  obtain ⟨m, hm, hfm⟩ := hs.exists_fixed_lift H3 hc₀R hfix
  have hcR : c₀ * m ∈ R := R.mul_mem hc₀R (hs.N_le_R hm)
  have hcC : c₀ * m ∈ R ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine ⟨hcR, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc (c₀ * m) * t = (t * (c₀ * m) * t⁻¹) * t := by rw [hfm]
      _ = t * (c₀ * m) := by group
  have hv' : (c₀ * m)⁻¹ * (u * v) ∈ V := by
    have e : (c₀ * m)⁻¹ * (u * v) = m⁻¹ * (t * u * t⁻¹)⁻¹ * v := by rw [hc₀]; group
    rw [e]
    exact V.mul_mem (V.mul_mem (V.inv_mem (hs.N_le_V hm)) (V.inv_mem hτu)) hv
  have e : u * v = (c₀ * m) * ((c₀ * m)⁻¹ * (u * v)) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcC) (Subgroup.mem_sup_right hv')

omit [Finite G] in
theorem C_inf_V_eq :
    (R ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ V = N ⊓ Subgroup.centralizer ({t} : Set G) := by
  apply le_antisymm
  · rintro x ⟨⟨hxR, hxc⟩, hxV⟩
    have hc := Subgroup.mem_centralizer_singleton_iff.1 hxc
    exact ⟨hs.fixed_V hxV hc.symm, hxc⟩
  · rintro x ⟨hxN, hxc⟩
    exact ⟨⟨hs.N_le_R hxN, hxc⟩, hs.N_le_V hxN⟩

theorem card_C
    (H3 : ∀ n ∈ N, (t * n * t⁻¹) * n = 1 → ∃ m ∈ N, n = (t * m * t⁻¹) * m⁻¹) :
    Nat.card (R ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) * Nat.card N =
      Nat.card U * Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
  set C := R ⊓ Subgroup.centralizer ({t} : Set G) with hC
  have hCV : C ≤ Subgroup.normalizer (V : Set G) := inf_le_left.trans hs.V_norm
  have h1 := card_sup_mul_card_inf hCV
  have hCsup : C ⊔ V = R := le_antisymm (sup_le inf_le_left hs.V_le) (hs.R_le_C_sup_V H3)
  rw [hCsup, hC, hs.C_inf_V_eq] at h1
  have hUV : U ≤ Subgroup.normalizer (V : Set G) := hs.U_le.trans hs.V_norm
  have h2 := card_sup_mul_card_inf hUV
  rw [← hs.R_eq, hs.inf_eq] at h2
  have hVpos : 0 < Nat.card V := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hVpos
  calc Nat.card C * Nat.card N * Nat.card V
      = (Nat.card C * Nat.card V) * Nat.card N := by ring
    _ = (Nat.card R * Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) *
        Nat.card N := by rw [← h1]
    _ = Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
        (Nat.card R * Nat.card N) := by ring
    _ = Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
        (Nat.card U * Nat.card V) := by rw [h2]
    _ = Nat.card U * Nat.card (N ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) *
        Nat.card V := by ring

end Finite

end SwapData

end Swap

end CFSG.QuasithinUnique.Lin2
