module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Invol

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open Sec2V4
open scoped Pointwise

namespace Sec2

variable {G : Type} [Group G] {S Z H : Subgroup G} {x t z : G}

theorem Coord.comm_eq_of_Ψ_eq (C : Coord S Z H) (hS : Special S Z) {a a' b b' : G}
    (ha : a ∈ S) (ha' : a' ∈ S) (hb : b ∈ S) (hb' : b' ∈ S) (h1 : C.Ψ a = C.Ψ a')
    (h2 : C.Ψ b = C.Ψ b') : a * b * a⁻¹ * b⁻¹ = a' * b' * a'⁻¹ * b'⁻¹ := by
  have hc : a' * a⁻¹ ∈ Z := (C.Ψ_eq_iff hS ha' ha).mp h1.symm
  have hd : b' * b⁻¹ ∈ Z := (C.Ψ_eq_iff hS hb' hb).mp h2.symm
  have hd' : b⁻¹ * b' ∈ Z := by
    have e : b⁻¹ * b' = b⁻¹ * (b' * b⁻¹) * b := by group
    rw [e, hS.conj_Z' hd hb]
    exact hd
  obtain ⟨c, hcZ, rfl⟩ : ∃ c ∈ Z, a' = c * a := ⟨a' * a⁻¹, hc, by group⟩
  obtain ⟨d, hdZ, rfl⟩ : ∃ d ∈ Z, b' = b * d := ⟨b⁻¹ * b', hd', by group⟩
  rw [hS.comm_mul_Z ha' hb hdZ, hS.comm_mul_left (hS.le hcZ) ha hb]
  have h3 : c * b * c⁻¹ * b⁻¹ = 1 := by
    rw [hS.comm_Z hcZ hb]
    group
  rw [h3, one_mul]

theorem Coord.sq_eq_of_Ψ_eq (C : Coord S Z H) (hS : Special S Z) {a a' : G} (ha : a ∈ S)
    (ha' : a' ∈ S) (h : C.Ψ a = C.Ψ a') : a * a = a' * a' := by
  have hc : a * a'⁻¹ ∈ Z := (C.Ψ_eq_iff hS ha ha').mp h
  obtain ⟨c, hcZ, rfl⟩ : ∃ c ∈ Z, a = c * a' := ⟨a * a'⁻¹, hc, by group⟩
  calc c * a' * (c * a') = c * (a' * c) * a' := by group
    _ = c * (c * a') * a' := by rw [hS.comm_Z hcZ ha']
    _ = (c * c) * (a' * a') := by group
    _ = a' * a' := by rw [hS.elem c hcZ, one_mul]

theorem conj_eq_of_mem_zpowers (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) (hzZ : z ∈ Z)
    {c : G} (hc : c ∈ zpowers z) : t * c * t⁻¹ = c :=
  (hz c (zpowers_le.mpr hzZ hc)).mpr hc

theorem exists_mem_Z_not_mem [Finite G] (hS : Special S Z) (hz1 : z ≠ 1) (hzZ : z ∈ Z) :
    ∃ c ∈ Z, c ∉ zpowers z := by
  by_contra h
  push Not at h
  have hle : Z ≤ zpowers z := fun c hc => h c hc
  have h1 := Subgroup.card_le_of_le hle
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [sq]; exact hS.elem z hzZ) hz1
  rw [hS.card, Nat.card_zpowers, hz2] at h1
  omega

theorem Coord.nondeg [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) {c : G} (hc : c ∈ Z) (hc1 : c ≠ 1) :
    ∀ s ∈ S, (∀ u ∈ S, s * u * s⁻¹ * u⁻¹ ∈ zpowers c) → s ∈ Z :=
  fun _ hs hsc =>
    C.mem_of_comm_mem_zpowers hS hHS hx.normS hx.normZ hx.cube hx.closure hc hc1 hs hsc

theorem XData.sq_eq (hx : XData S Z x) : x * x = x⁻¹ := by
  calc x * x = x ^ 3 * x⁻¹ := by rw [pow_three]; group
    _ = x⁻¹ := by rw [hx.cube, one_mul]

theorem Coord.Ψ_conj_inv (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x) {w : G}
    (hw : w ∈ S) : C.Ψ (x⁻¹ * w * x) = C.Ψ w + C.Ψ (x * w * x⁻¹) := by
  have hxS : x * w * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx.normS w).mp hw
  have hxS' : x⁻¹ * w * x ∈ S := by
    have := (mem_normalizer_iff.mp (inv_mem hx.normS) w).mp hw
    simpa using this
  have hsc := hx.scalar w hw
  have e2 : x⁻¹ * x⁻¹ * w * x * x = x * w * x⁻¹ := by
    calc x⁻¹ * x⁻¹ * w * x * x = (x * x)⁻¹ * w * (x * x) := by group
      _ = x * w * x⁻¹ := by rw [hx.sq_eq, inv_inv]
  rw [e2] at hsc
  have h3 := (C.Ψ_eq_zero_iff hS (S.mul_mem (S.mul_mem hw hxS') hxS)).mpr hsc
  rw [C.Ψ_mul hS (S.mul_mem hw hxS') hxS, C.Ψ_mul hS hw hxS'] at h3
  calc C.Ψ (x⁻¹ * w * x) = C.Ψ (x⁻¹ * w * x) + (C.Ψ w + C.Ψ (x * w * x⁻¹) +
        (C.Ψ w + C.Ψ (x * w * x⁻¹))) := by rw [pair_add_self, add_zero]
    _ = (C.Ψ w + C.Ψ (x⁻¹ * w * x) + C.Ψ (x * w * x⁻¹)) + (C.Ψ w + C.Ψ (x * w * x⁻¹)) := by
        abel
    _ = C.Ψ w + C.Ψ (x * w * x⁻¹) := by rw [h3, zero_add]

theorem XData.conj_ne (hS : Special S Z) (hx : XData S Z x) {d : G} (hd : d ∈ Z) (hd1 : d ≠ 1) :
    x * d * x⁻¹ ≠ d := by
  intro h
  have hbot : Subgroup.closure {c | ∃ w ∈ Z, c = w⁻¹ * x⁻¹ * w * x} = ⊥ := by
    rw [closure_eq_bot_iff]
    rintro _ ⟨w, hw, rfl⟩
    have h1 := hS.conj_eq_of_conj_eq hx.normZ hx.cube hd hd1 h hw
    calc w⁻¹ * x⁻¹ * w * x = w⁻¹ * x⁻¹ * (x * w * x⁻¹) * x := by rw [h1]
      _ = 1 := by group
  have h4 := hS.card
  rw [← hx.closure, hbot, card_bot] at h4
  norm_num at h4

theorem Coord.Ψ_t_conj_x (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) {w : G} (hw : w ∈ hS.Wt t) :
    C.Ψ (t * (x * w * x⁻¹) * t⁻¹) = C.Ψ w + C.Ψ (x * w * x⁻¹) := by
  have hconjS : t * w * t⁻¹ ∈ S := (mem_normalizer_iff.mp ht.normS w).mp hw.1
  have e : t * (x * w * x⁻¹) * t⁻¹ = x⁻¹ * (t * w * t⁻¹) * x⁻¹⁻¹ := by
    calc t * (x * w * x⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * w * t⁻¹) * (t * x * t⁻¹)⁻¹ := by group
      _ = x⁻¹ * (t * w * t⁻¹) * x⁻¹⁻¹ := by rw [ht.inv]
  rw [e, C.Ψ_conj_eq hS (inv_mem hx.normS) hconjS hw.1 ((C.mem_Wt_iff hS ht.normS hw.1).mp hw),
    inv_inv, C.Ψ_conj_inv hS hx hw.1]

theorem Coord.comm_conj_x_mem (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {w b : G}
    (hw : w ∈ hS.Wt t) (hb : b ∈ hS.Wt t) (hwb : w * b * w⁻¹ * b⁻¹ = 1) :
    w * (x * b * x⁻¹) * w⁻¹ * (x * b * x⁻¹)⁻¹ ∈ zpowers z := by
  have hxb : x * b * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx.normS b).mp hb.1
  have htw : t * w * t⁻¹ ∈ S := (mem_normalizer_iff.mp ht.normS w).mp hw.1
  have htxb : t * (x * b * x⁻¹) * t⁻¹ ∈ S := (mem_normalizer_iff.mp ht.normS _).mp hxb
  refine (hz _ (hS.comm_mem hw.1 hxb)).mp ?_
  have e : t * (w * (x * b * x⁻¹) * w⁻¹ * (x * b * x⁻¹)⁻¹) * t⁻¹ =
      (t * w * t⁻¹) * (t * (x * b * x⁻¹) * t⁻¹) * (t * w * t⁻¹)⁻¹ *
        (t * (x * b * x⁻¹) * t⁻¹)⁻¹ := by group
  have hΨ : C.Ψ (t * (x * b * x⁻¹) * t⁻¹) = C.Ψ (b * (x * b * x⁻¹)) := by
    rw [C.Ψ_t_conj_x hS hx ht hb, C.Ψ_mul hS hb.1 hxb]
  rw [e, C.comm_eq_of_Ψ_eq hS htw hw.1 htxb (S.mul_mem hb.1 hxb)
    ((C.mem_Wt_iff hS ht.normS hw.1).mp hw) hΨ, hS.comm_mul_right hw.1 hb.1 hxb, hwb, one_mul]

theorem Coord.card_img_Wt [Finite G] (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) :
    Nat.card (C.img hS (hS.Wt t)) = 16 ∧
      Nat.card (C.img hS ((hS.Wt t).map (MulAut.conj x).toMonoidHom)) = 16 := by
  have hcardW := C.card_Wt hS hx ht
  constructor
  · have := C.card_eq_four_mul hS (hS.Z_le_Wt ht.normS) hS.Wt_le
    omega
  · have h1 := C.card_eq_four_mul hS (hS.Z_le_Wtx hx ht) (hS.Wtx_le hx)
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hcardW] at h1
    omega

theorem Coord.exists_decomp [Finite G] (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) {s : G} (hs : s ∈ S) :
    ∃ a ∈ hS.Wt t, ∃ b ∈ hS.Wt t, C.Ψ s = C.Ψ (a * (x * b * x⁻¹)) := by
  obtain ⟨h16, h16x⟩ := C.card_img_Wt hS hx ht
  obtain ⟨_, ⟨a, ha, rfl⟩, _, ⟨u, hu, rfl⟩, hab⟩ := exists_add_of_inf_eq_bot
    (fun m hm => C.img_even hS hm) (fun m hm => C.img_even hS hm) (C.img_Wt_inf hS hx ht)
    h16.ge h16x.ge (C.Ψ_even hS hs)
  obtain ⟨b, hb, hbu⟩ := hu.1
  have hbu' : u = x * b * x⁻¹ := by
    rw [← hbu]
    rfl
  subst hbu'
  refine ⟨a, ha.1, b, hb, ?_⟩
  rw [C.Ψ_mul hS ha.2 hu.2, hab]

theorem Coord.exists_not_comm_Wt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) :
    ∃ w ∈ hS.Wt t, ∃ w' ∈ hS.Wt t, w * w' * w⁻¹ * w'⁻¹ ≠ 1 := by
  by_contra habel
  push Not at habel
  have hWZ : hS.Wt t ≤ Z := by
    intro w hw
    refine C.nondeg hS hHS hx hzZ hz1 w hw.1 fun s hs => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := C.exists_decomp hS hx ht hs
    have hxb : x * b * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx.normS b).mp hb.1
    rw [C.comm_eq_of_Ψ_eq hS hw.1 hw.1 hs (S.mul_mem ha.1 hxb) rfl hab,
      hS.comm_mul_right hw.1 ha.1 hxb, habel w hw a ha, one_mul]
    exact C.comm_conj_x_mem hS hx ht hz hw hb (habel w hw b hb)
  have h1 := Subgroup.card_le_of_le hWZ
  rw [C.card_Wt hS hx ht, hS.card] at h1
  omega

theorem Coord.mem_Z_of_comm_Wt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {w : G}
    (hw : w ∈ hS.Wt t) (hc : ∀ w' ∈ hS.Wt t, w * w' = w' * w) : w ∈ Z := by
  by_contra hwZ
  let R : Subgroup G := hS.Wt t ⊓ Subgroup.centralizer (hS.Wt t : Set G)
  have hZR : Z ≤ R := fun c hc' =>
    ⟨hS.Z_le_Wt ht.normS hc', mem_centralizer_iff.mpr fun h hh => (hS.comm_Z hc' hh.1).symm⟩
  have hRW : R ≤ hS.Wt t := inf_le_left
  have hinv : ∀ h ∈ H, ∀ u ∈ R, h * u * h⁻¹ ∈ R := by
    intro h hh u hu
    refine ⟨C.conj_mem_Wt hS hHS ht hh hu.1, mem_centralizer_iff.mpr fun w' hw' => ?_⟩
    have hw'' : h⁻¹ * w' * h ∈ hS.Wt t := by
      have := C.conj_mem_Wt hS hHS ht (H.inv_mem hh) hw'
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp hu.2 _ hw''
    calc w' * (h * u * h⁻¹) = h * ((h⁻¹ * w' * h) * u) * h⁻¹ := by group
      _ = h * (u * (h⁻¹ * w' * h)) * h⁻¹ := by rw [h1]
      _ = h * u * h⁻¹ * w' := by group
  have hwR : w ∈ R := ⟨hw, mem_centralizer_iff.mpr fun w' hw' => (hc w' hw').symm⟩
  have heq := C.eq_Wt_of_invariant hS hHS hx ht hZR hRW hinv ⟨w, hwR, hwZ⟩
  obtain ⟨a, ha, b, hb, hab⟩ := C.exists_not_comm_Wt hS hHS hx ht hzZ hz1 hz
  apply hab
  have ha' : a ∈ R := heq ▸ ha
  have h1 := mem_centralizer_iff.mp ha'.2 b hb
  rw [← h1]
  group

theorem vec_add_self (v : Fin 5 → ZMod 2) : v + v = 0 := by
  funext k
  exact (by decide : ∀ c : ZMod 2, c + c = 0) (v k)

theorem pair_eq_of_add_eq_zero {m m' : Pair} (h : m + m' = 0) : m = m' := by
  calc m = m + (m' + m') := by rw [pair_add_self, add_zero]
    _ = (m + m') + m' := by rw [add_assoc]
    _ = m' := by rw [h, zero_add]

theorem Coord.Ψ_eq_of_proj_eq (C : Coord S Z H) (hS : Special S Z)
    {π : Pair →+ (Fin 5 → ZMod 2)} (hinj : ∀ m ∈ C.img hS (hS.Wt t), π m = 0 → m = 0) {a b : G}
    (ha : a ∈ hS.Wt t) (hb : b ∈ hS.Wt t) (h : π (C.Ψ a) = π (C.Ψ b)) : C.Ψ a = C.Ψ b := by
  have hm : C.Ψ a + C.Ψ b ∈ C.img hS (hS.Wt t) := by
    rw [← C.Ψ_mul hS ha.1 hb.1]
    exact C.Ψ_mem_img hS ((hS.Wt t).mul_mem ha hb) (S.mul_mem ha.1 hb.1)
  have h0 : π (C.Ψ a + C.Ψ b) = 0 := by
    rw [map_add, h, vec_add_self]
  exact pair_eq_of_add_eq_zero (hinj _ hm h0)

theorem sq_mul_eq (hS : Special S Z) {a b : G} (ha : a ∈ S) (hb : b ∈ S) :
    (a * b) * (a * b) = (a * a) * (a * b * a⁻¹ * b⁻¹) * (b * b) := by
  have hκ : a⁻¹ * b * a * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
    have hc := hS.comm_mem hb ha
    have e : a⁻¹ * b * a * b⁻¹ = a⁻¹ * (b * a * b⁻¹ * a⁻¹) * a := by group
    rw [e, hS.conj_Z' hc ha, ← hS.inv_eq hc, Special.comm_inv]
  rw [← hκ]
  group

theorem Coord.exists_proj_sq_Wt [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) :
    ∃ π : Pair →+ (Fin 5 → ZMod 2), (∀ σ m, π (act₂ σ m) = act σ (π m)) ∧
      (∀ m ∈ C.img hS (hS.Wt t), π m = 0 → m = 0) ∧ (∀ m ∈ C.img hS (hS.Wt t), IsEven (π m)) ∧
      (∀ v, IsEven v → ∃ m ∈ C.img hS (hS.Wt t), π m = v) ∧
      ∀ w ∈ hS.Wt t, (w * w = 1 ↔ q₀ (π (C.Ψ w)) = 0) := by
  obtain ⟨π, hπ, hinj, heven, honto⟩ := C.exists_proj_Wt hS hHS hx ht
  refine ⟨π, hπ, hinj, heven, honto, ?_⟩
  obtain ⟨c', hc'Z, hc'z⟩ := exists_mem_Z_not_mem hS hz1 hzZ
  have hc'1 : c' ≠ 1 := fun h => hc'z (h ▸ one_mem _)
  have hzc' : z ≠ c' := fun h => hc'z (h ▸ mem_zpowers z)
  have hevenW : ∀ w ∈ hS.Wt t, IsEven (π (C.Ψ w)) := fun w hw =>
    heven _ (C.Ψ_mem_img hS hw hw.1)
  have hlift : ∀ v : Fin 5 → ZMod 2, IsEven v → ∃ w ∈ hS.Wt t, π (C.Ψ w) = v := by
    intro v hv
    obtain ⟨m, ⟨w, hw, rfl⟩, hmv⟩ := honto v hv
    exact ⟨w, hw.1, hmv⟩
  choose! L hL hLπ using hlift
  let q : (Fin 5 → ZMod 2) → ZMod 2 := fun v => Special.ell c' (L v * L v)
  have hq : ∀ w ∈ hS.Wt t, q (π (C.Ψ w)) = Special.ell c' (w * w) := by
    intro w hw
    have hv := hevenW w hw
    have h1 := C.Ψ_eq_of_proj_eq hS hinj (hL _ hv) hw (hLπ _ hv)
    show Special.ell c' (L _ * L _) = _
    rw [C.sq_eq_of_Ψ_eq hS (hL _ hv).1 hw.1 h1]
  have hpol : ∀ a ∈ hS.Wt t, ∀ b ∈ hS.Wt t, Special.ell c' ((a * b) * (a * b)) =
      Special.ell c' (a * a) + Special.ell c' (a * b * a⁻¹ * b⁻¹) + Special.ell c' (b * b) := by
    intro a ha b hb
    rw [sq_mul_eq hS ha.1 hb.1, hS.ell_mul hc'Z hc'1 (Z.mul_mem (hS.sq a ha.1)
      (hS.comm_mem ha.1 hb.1)) (hS.sq b hb.1), hS.ell_mul hc'Z hc'1 (hS.sq a ha.1)
      (hS.comm_mem ha.1 hb.1)]
  have hπmul : ∀ a ∈ hS.Wt t, ∀ b ∈ hS.Wt t,
      π (C.Ψ (a * b)) = π (C.Ψ a) + π (C.Ψ b) := fun a ha b hb => by
    rw [C.Ψ_mul hS ha.1 hb.1, map_add]
  have hinv : ∀ σ ∈ alternatingGroup (Fin 5), ∀ v, IsEven v → q (act σ v) = q v := by
    intro σ hσ v hv
    obtain ⟨h, hh⟩ := C.surj ⟨σ, hσ⟩
    have hw := hL v hv
    have hhw : (h : G) * L v * (h : G)⁻¹ ∈ hS.Wt t := C.conj_mem_Wt hS hHS ht h.2 hw
    have e1 : π (C.Ψ ((h : G) * L v * (h : G)⁻¹)) = act σ v := by
      rw [C.Ψ_conj hS h hw.1, hπ, hLπ v hv, hh]
    have e2 : ((h : G) * L v * (h : G)⁻¹) * ((h : G) * L v * (h : G)⁻¹) =
        (h : G) * (L v * L v) * (h : G)⁻¹ := by group
    rw [← e1, hq _ hhw, e2, C.conj_eq_of_mem_H hS hHS h.2 (hS.sq _ hw.1)]
  have hadd : ∀ u v w, IsEven u → IsEven v → IsEven w →
      q (u + v + w) + q (u + v) + q w = (q (u + w) + q u + q w) + (q (v + w) + q v + q w) := by
    intro u v w hu hv hw
    have ha := hL u hu
    have hb := hL v hv
    have hc := hL w hw
    have hab := (hS.Wt t).mul_mem ha hb
    rw [← hLπ u hu, ← hLπ v hv, ← hLπ w hw, ← hπmul _ ha _ hb, ← hπmul _ hab _ hc,
      ← hπmul _ ha _ hc, ← hπmul _ hb _ hc, hq _ ((hS.Wt t).mul_mem hab hc), hq _ hab, hq _ hc,
      hq _ ((hS.Wt t).mul_mem ha hc), hq _ ha, hq _ ((hS.Wt t).mul_mem hb hc), hq _ hb,
      hpol _ hab _ hc, hpol _ ha _ hc, hpol _ hb _ hc,
      hS.comm_mul_left ha.1 hb.1 hc.1,
      hS.ell_mul hc'Z hc'1 (hS.comm_mem ha.1 hc.1) (hS.comm_mem hb.1 hc.1)]
    generalize Special.ell c' (L u * L v * (L u * L v)) = A
    generalize Special.ell c' (L w * L w) = C2
    generalize Special.ell c' (L u * L u) = A2
    generalize Special.ell c' (L v * L v) = B2
    generalize Special.ell c' (L u * L w * (L u)⁻¹ * (L w)⁻¹) = P1
    generalize Special.ell c' (L v * L w * (L v)⁻¹ * (L w)⁻¹) = P2
    revert A C2 A2 B2 P1 P2
    decide
  have hne : ∃ v w, IsEven v ∧ IsEven w ∧ q (v + w) + q v + q w ≠ 0 := by
    obtain ⟨a, ha, b, hb, hab⟩ := C.exists_not_comm_Wt hS hHS hx ht hzZ hz1 hz
    refine ⟨π (C.Ψ a), π (C.Ψ b), hevenW a ha, hevenW b hb, ?_⟩
    rw [← hπmul _ ha _ hb, hq _ ((hS.Wt t).mul_mem ha hb), hq _ ha, hq _ hb, hpol _ ha _ hb]
    have hcz : a * b * a⁻¹ * b⁻¹ = z := by
      rcases hS.eq_one_or_eq hzZ (comm_mem_zpowers hS hz ha hb) with h | h
      · exact absurd h hab
      · exact h
    have hell : Special.ell c' z = 1 := by
      rcases zmod2_cases (Special.ell c' z) with h | h
      · exfalso
        rw [Special.ell_eq_zero_iff] at h
        rcases hS.eq_one_or_eq hc'Z h with h' | h'
        · exact hz1 h'
        · exact hzc' h'
      · exact h
    rw [hcz, hell]
    generalize Special.ell c' (a * a) = A2
    generalize Special.ell c' (b * b) = B2
    revert A2 B2
    decide
  have hq₀ := fun u hu => eq_q₀ hinv hadd hne (u := u) hu
  intro w hw
  rw [← hq₀ _ (hevenW w hw), hq w hw, Special.ell_eq_zero_iff]
  constructor
  · intro h
    rw [h]
    exact one_mem _
  · intro h
    exact hS.inf_zpowers hzZ hc'Z hzc' (sq_mem_zpowers hS hz hw) h

theorem Coord.card_le_eight_of_elem [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {U : Subgroup G}
    (hUW : U ≤ hS.Wt t) (hsq : ∀ u ∈ U, u * u = 1)
    (hcomm : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u) :
    Nat.card U ≤ 8 ∧ (Nat.card U = 8 → Z ≤ U) := by
  classical
  obtain ⟨π, -, hinj, heven, -, hq⟩ := C.exists_proj_sq_Wt hS hHS hx ht hzZ hz1 hz
  have hdep : ∀ m ∈ C.img hS U, ∀ m' ∈ C.img hS U, m ≠ 0 → m' ≠ 0 → m = m' := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨u', hu', rfl⟩ h0 h0'
    by_contra hne
    have huW := hUW hu.1
    have hu'W := hUW hu'.1
    have hv0 : π (C.Ψ u) ≠ 0 := fun h => h0 (hinj _ (C.Ψ_mem_img hS huW hu.2) h)
    have hw0 : π (C.Ψ u') ≠ 0 := fun h => h0' (hinj _ (C.Ψ_mem_img hS hu'W hu'.2) h)
    have hvw : π (C.Ψ u) ≠ π (C.Ψ u') := fun h => hne (C.Ψ_eq_of_proj_eq hS hinj huW hu'W h)
    have hqv := (hq u huW).mp (hsq u hu.1)
    have hqw := (hq u' hu'W).mp (hsq u' hu'.1)
    have huu' : (u * u') * (u * u') = 1 := by
      calc (u * u') * (u * u') = u * (u' * u) * u' := by group
        _ = u * (u * u') * u' := by rw [hcomm u' hu'.1 u hu.1]
        _ = (u * u) * (u' * u') := by group
        _ = 1 := by rw [hsq u hu.1, hsq u' hu'.1, one_mul]
    have hq3 := (hq _ ((hS.Wt t).mul_mem huW hu'W)).mp huu'
    rw [C.Ψ_mul hS hu.2 hu'.2, map_add, q₀_add_eq_one _ _ (heven _ (C.Ψ_mem_img hS huW hu.2))
      (heven _ (C.Ψ_mem_img hS hu'W hu'.2)) hv0 hw0 hvw hqv hqw] at hq3
    exact one_ne_zero hq3
  have himg : Nat.card (C.img hS U) ≤ 2 := by
    have hf : Function.Injective (fun m : C.img hS U => decide ((m : Pair) = 0)) := by
      intro m m' h
      by_cases hm : (m : Pair) = 0 <;> by_cases hm' : (m' : Pair) = 0
      · exact Subtype.ext (hm.trans hm'.symm)
      · simp [hm, hm'] at h
      · simp [hm, hm'] at h
      · exact Subtype.ext (hdep _ m.2 _ m'.2 hm hm')
    have := Nat.card_le_card_of_injective _ hf
    simpa using this
  have h1 := C.card_eq hS (hUW.trans hS.Wt_le)
  have h2 : Nat.card (U ⊓ Z : Subgroup G) ≤ 4 := hS.card ▸ Subgroup.card_le_of_le inf_le_right
  refine ⟨by rw [h1]; nlinarith, fun h8 => ?_⟩
  have h3 : Nat.card (U ⊓ Z : Subgroup G) = 4 := by
    rw [h8] at h1
    have : 0 < Nat.card (C.img hS U) := Nat.card_pos
    nlinarith
  have h4 : U ⊓ Z = Z := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hS.card])
  exact h4 ▸ inf_le_left

@[expose] def Coord.fixS (C : Coord S Z H) (hS : Special S Z)
    (E : Subgroup (alternatingGroup (Fin 5))) : Subgroup G where
  carrier := {s | s ∈ S ∧ ∀ σ ∈ E, act₂ (σ : Equiv.Perm (Fin 5)) (C.Ψ s) = C.Ψ s}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨S.mul_mem ha hb, fun σ hσ => ?_⟩
    rw [C.Ψ_mul hS ha hb]
    show act₂ _ (C.Ψ a) + act₂ _ (C.Ψ b) = _
    rw [ha' σ hσ, hb' σ hσ]
  one_mem' := ⟨S.one_mem, fun σ _ => by rw [C.Ψ_one]; rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨S.inv_mem ha, fun σ hσ => by rw [C.Ψ_inv hS ha]; exact ha' σ hσ⟩

theorem Coord.Z_le_fixS (C : Coord S Z H) (hS : Special S Z)
    (E : Subgroup (alternatingGroup (Fin 5))) : Z ≤ C.fixS hS E := fun c hc =>
  ⟨hS.le hc, fun σ _ => by rw [(C.Ψ_eq_zero_iff hS (hS.le hc)).mpr hc]; rfl⟩

theorem proj_inj {N : AddSubgroup Pair} {π : Pair →+ (Fin 5 → ZMod 2)}
    (hinj : ∀ m ∈ N, π m = 0 → m = 0) {m m' : Pair} (hm : m ∈ N) (hm' : m' ∈ N)
    (h : π m = π m') : m = m' :=
  pair_eq_of_add_eq_zero (hinj _ (N.add_mem hm hm') (by rw [map_add, h, vec_add_self]))

theorem inj_pair2 {a b : Pair} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    Function.Injective
      (fun p : Bool × Bool => (if p.1 then a else 0) + (if p.2 then b else 0)) := by
  have h1 : a + b ≠ 0 := fun h => hab (pair_eq_of_add_eq_zero h)
  have h2 : a + b ≠ a := fun h => hb (by
    calc b = a + b + a := by rw [add_comm a b, add_assoc, pair_add_self, add_zero]
      _ = a + a := by rw [h]
      _ = 0 := pair_add_self a)
  have h3 : a + b ≠ b := fun h => ha (by
    calc a = a + b + b := by rw [add_assoc, pair_add_self, add_zero]
      _ = b + b := by rw [h]
      _ = 0 := pair_add_self b)
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, zero_add] at h <;>
    first
    | rfl
    | (exfalso
       first
       | exact ha h | exact ha h.symm | exact hb h | exact hb h.symm | exact hab h
       | exact hab h.symm | exact h1 h | exact h1 h.symm | exact h2 h | exact h2 h.symm
       | exact h3 h | exact h3 h.symm)

theorem eq_of_decide_eq {a b v : Fin 5 → ZMod 2} (hv : v ≠ 0) (ha : a = 0 ∨ a = v)
    (hb : b = 0 ∨ b = v) (h : decide (a = 0) = decide (b = 0)) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

theorem Coord.conj_x_mem_fixS (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (hxH : x ∈ normalizer (H : Set G))
    (hxH' : ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S) {E : Subgroup (alternatingGroup (Fin 5))} {s : G}
    (hs : s ∈ C.fixS hS E) : x * s * x⁻¹ ∈ C.fixS hS E := by
  have hxs : x * s * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx.normS s).mp hs.1
  refine ⟨hxs, fun σ hσ => ?_⟩
  obtain ⟨h, hh⟩ := C.surj σ
  have hk : x⁻¹ * (h : G) * x ∈ H := by
    have := (mem_normalizer_iff.mp (inv_mem hxH) h).mp h.2
    simpa using this
  have hφ : C.φ ⟨x⁻¹ * (h : G) * x, hk⟩ = C.φ h := by
    have hker : (⟨x⁻¹ * (h : G) * x, hk⟩⁻¹ * h : ↥H) ∈ C.φ.ker := by
      rw [C.ker, mem_subgroupOf]
      show (x⁻¹ * (h : G) * x)⁻¹ * (h : G) ∈ S
      have e : (x⁻¹ * (h : G) * x)⁻¹ * (h : G) = x⁻¹ * (h : G)⁻¹ * x * h := by group
      rw [e]
      exact hxH' h h.2
    have := MonoidHom.mem_ker.mp hker
    rw [map_mul, map_inv, inv_mul_eq_one] at this
    exact this
  have hks : (x⁻¹ * (h : G) * x) * s * (x⁻¹ * (h : G) * x)⁻¹ ∈ S :=
    (mem_normalizer_iff.mp (hHS hk) s).mp hs.1
  have h1 : C.Ψ ((x⁻¹ * (h : G) * x) * s * (x⁻¹ * (h : G) * x)⁻¹) = C.Ψ s := by
    have h3 := C.Ψ_conj hS ⟨x⁻¹ * (h : G) * x, hk⟩ hs.1
    rw [hφ, hh, hs.2 σ hσ] at h3
    exact h3
  have e : (h : G) * (x * s * x⁻¹) * (h : G)⁻¹ =
      x * ((x⁻¹ * (h : G) * x) * s * (x⁻¹ * (h : G) * x)⁻¹) * x⁻¹ := by group
  have h2 := C.Ψ_conj hS h hxs
  rw [hh] at h2
  rw [← h2, e, C.Ψ_conj_eq hS hx.normS hks hs.1 h1]

theorem card_le_two_of_forall {N : AddSubgroup Pair} {m₀ : Pair}
    (h : ∀ m ∈ N, m = 0 ∨ m = m₀) : Nat.card N ≤ 2 := by
  classical
  have hf : Function.Injective (fun m : N => decide ((m : Pair) = 0)) := by
    intro m m' hmm
    rcases h _ m.2 with h1 | h1 <;> rcases h _ m'.2 with h2 | h2
    · exact Subtype.ext (h1.trans h2.symm)
    · by_cases h0 : m₀ = 0
      · exact Subtype.ext (h1.trans (h2.trans h0).symm)
      · simp only [h1, h2, h0, decide_true, decide_false] at hmm
        exact absurd hmm (by decide)
    · by_cases h0 : m₀ = 0
      · exact Subtype.ext ((h1.trans h0).trans h2.symm)
      · simp only [h1, h2, h0, decide_true, decide_false] at hmm
        exact absurd hmm (by decide)
    · exact Subtype.ext (h1.trans h2.symm)
  have := Nat.card_le_card_of_injective _ hf
  simpa using this

theorem card_le_four_of_forall {N : AddSubgroup Pair} {v₀ : Fin 5 → ZMod 2} (hv₀ : v₀ ≠ 0)
    (h : ∀ m ∈ N, (m.1 = 0 ∨ m.1 = v₀) ∧ (m.2 = 0 ∨ m.2 = v₀)) : Nat.card N ≤ 4 := by
  classical
  have hf : Function.Injective (fun m : N =>
      (decide ((m : Pair).1 = 0), decide ((m : Pair).2 = 0))) := by
    intro m m' hmm
    obtain ⟨h1, h2⟩ := Prod.mk.inj hmm
    exact Subtype.ext (Prod.ext (eq_of_decide_eq hv₀ (h _ m.2).1 (h _ m'.2).1 h1)
      (eq_of_decide_eq hv₀ (h _ m.2).2 (h _ m'.2).2 h2))
  have := Nat.card_le_card_of_injective _ hf
  simpa using this

theorem Coord.card_img_fixS_le (C : Coord S Z H) (hS : Special S Z)
    {E : Subgroup (alternatingGroup (Fin 5))} (hE : Nat.card E = 4) :
    Nat.card (C.img hS (C.fixS hS E)) ≤ 4 := by
  obtain ⟨v₀, -, hv₀0, -, hfix⟩ := exists_fixed_iff E hE
  refine card_le_four_of_forall hv₀0 ?_
  rintro _ ⟨s, hs, rfl⟩
  have hev := C.Ψ_even hS hs.2
  exact ⟨(hfix _ hev.1).mp fun σ hσ => congrArg Prod.fst (hs.1.2 σ hσ),
    (hfix _ hev.2).mp fun σ hσ => congrArg Prod.snd (hs.1.2 σ hσ)⟩

theorem Coord.exists_w₀ [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (ht : TData S H x t) (hzZ : z ∈ Z)
    (hz1 : z ≠ 1) (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z))
    {E : Subgroup (alternatingGroup (Fin 5))} (hE : Nat.card E = 4) :
    ∃ w₀ ∈ hS.Wt t, w₀ ∈ C.fixS hS E ∧ w₀ ∉ Z ∧ w₀ * w₀ = 1 ∧
      ∀ s ∈ C.fixS hS E ⊓ hS.Wt t, C.Ψ s = 0 ∨ C.Ψ s = C.Ψ w₀ := by
  obtain ⟨π, hπ, hinj, heven, honto, hq⟩ := C.exists_proj_sq_Wt hS hHS hx ht hzZ hz1 hz
  obtain ⟨v₀, hv₀e, hv₀0, hq₀, hfix⟩ := exists_fixed_iff E hE
  have hv₀fix : ∀ σ ∈ E, act (σ : Equiv.Perm (Fin 5)) v₀ = v₀ := (hfix v₀ hv₀e).mpr (Or.inr rfl)
  obtain ⟨_, ⟨w₀, hw₀, rfl⟩, hm₀⟩ := honto v₀ hv₀e
  have himgW : ∀ w ∈ hS.Wt t, C.Ψ w ∈ C.img hS (hS.Wt t) := fun w hw => C.Ψ_mem_img hS hw hw.1
  have hw₀F : w₀ ∈ C.fixS hS E := by
    refine ⟨hw₀.2, fun σ hσ => ?_⟩
    have hmem : act₂ (σ : Equiv.Perm (Fin 5)) (C.Ψ w₀) ∈ C.img hS (hS.Wt t) :=
      C.img_invariant hS (fun h hh w hw => C.conj_mem_Wt hS hHS ht hh hw) hHS _ σ.2 _
        (himgW w₀ hw₀.1)
    exact proj_inj hinj hmem (himgW w₀ hw₀.1) (by rw [hπ, hm₀, hv₀fix σ hσ])
  refine ⟨w₀, hw₀.1, hw₀F, fun h => hv₀0 ?_, (hq w₀ hw₀.1).mpr (by rw [hm₀]; exact hq₀), ?_⟩
  · rw [← hm₀, (C.Ψ_eq_zero_iff hS hw₀.2).mpr h, map_zero]
  · intro s hs
    have hsW := hs.2
    have hfixπ : ∀ σ ∈ E, act (σ : Equiv.Perm (Fin 5)) (π (C.Ψ s)) = π (C.Ψ s) :=
      fun σ hσ => by rw [← hπ, hs.1.2 σ hσ]
    rcases (hfix _ (heven _ (himgW s hsW))).mp hfixπ with h | h
    · exact Or.inl (hinj _ (himgW s hsW) h)
    · exact Or.inr (proj_inj hinj (himgW s hsW) (himgW w₀ hw₀.1) (by rw [h, hm₀]))

theorem Coord.comm_conj_x_eq [Finite G] (C : Coord S Z H) (hS : Special S Z) (hx : XData S Z x)
    (ht : TData S H x t) (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z)) {w₀ : G} (hw₀ : w₀ ∈ hS.Wt t)
    (hw₀2 : w₀ * w₀ = 1) : w₀ * (x * w₀ * x⁻¹) = (x * w₀ * x⁻¹) * w₀ := by
  have hw₀S := hw₀.1
  have hw₁S : x * w₀ * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx.normS w₀).mp hw₀S
  have hγz := C.comm_conj_x_mem hS hx ht hz hw₀ hw₀ (by group)
  have hγZ := hS.comm_mem hw₀S hw₁S
  have hxw₁ : x * (x * w₀ * x⁻¹) * x⁻¹ ∈ S := (mem_normalizer_iff.mp hx.normS _).mp hw₁S
  have hw₁sq : (x * w₀ * x⁻¹) * (x * w₀ * x⁻¹) = 1 := by
    calc (x * w₀ * x⁻¹) * (x * w₀ * x⁻¹) = x * (w₀ * w₀) * x⁻¹ := by group
      _ = 1 := by rw [hw₀2]; group
  have hxγ : x * (w₀ * (x * w₀ * x⁻¹) * w₀⁻¹ * (x * w₀ * x⁻¹)⁻¹) * x⁻¹ =
      w₀ * (x * w₀ * x⁻¹) * w₀⁻¹ * (x * w₀ * x⁻¹)⁻¹ := by
    have e1 : x * (w₀ * (x * w₀ * x⁻¹) * w₀⁻¹ * (x * w₀ * x⁻¹)⁻¹) * x⁻¹ =
        (x * w₀ * x⁻¹) * (x * (x * w₀ * x⁻¹) * x⁻¹) * (x * w₀ * x⁻¹)⁻¹ *
          (x * (x * w₀ * x⁻¹) * x⁻¹)⁻¹ := by group
    have e3 : x * (x * w₀ * x⁻¹) * x⁻¹ = x⁻¹ * w₀ * x := by
      calc x * (x * w₀ * x⁻¹) * x⁻¹ = (x * x) * w₀ * (x * x)⁻¹ := by group
        _ = x⁻¹ * w₀ * x := by rw [hx.sq_eq, inv_inv]
    have e2 : C.Ψ (x * (x * w₀ * x⁻¹) * x⁻¹) = C.Ψ (w₀ * (x * w₀ * x⁻¹)) := by
      rw [e3, C.Ψ_conj_inv hS hx hw₀S, C.Ψ_mul hS hw₀S hw₁S]
    rw [e1, C.comm_eq_of_Ψ_eq hS hw₁S hw₁S hxw₁ (S.mul_mem hw₀S hw₁S) rfl e2,
      hS.comm_mul_right hw₁S hw₀S hw₁S]
    have e4 : (x * w₀ * x⁻¹) * (x * w₀ * x⁻¹) * (x * w₀ * x⁻¹)⁻¹ * (x * w₀ * x⁻¹)⁻¹ = 1 := by
      group
    rw [e4, mul_one, ← Special.comm_inv, hS.inv_eq hγZ]
  have hγ1 : w₀ * (x * w₀ * x⁻¹) * w₀⁻¹ * (x * w₀ * x⁻¹)⁻¹ = 1 := by
    rcases hS.eq_one_or_eq hzZ hγz with h | h
    · exact h
    · rw [h] at hxγ
      exact absurd hxγ (hx.conj_ne hS hzZ hz1)
  calc w₀ * (x * w₀ * x⁻¹) = (w₀ * (x * w₀ * x⁻¹) * w₀⁻¹ * (x * w₀ * x⁻¹)⁻¹) *
        (x * w₀ * x⁻¹) * w₀ := by group
    _ = (x * w₀ * x⁻¹) * w₀ := by rw [hγ1, one_mul]

theorem Coord.fixS_elem [Finite G] (C : Coord S Z H) (hS : Special S Z)
    (hHS : H ≤ normalizer (S : Set G)) (hx : XData S Z x) (hxH : x ∈ normalizer (H : Set G))
    (hxH' : ∀ h ∈ H, x⁻¹ * h⁻¹ * x * h ∈ S) (ht : TData S H x t) (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hz : ∀ c ∈ Z, (t * c * t⁻¹ = c ↔ c ∈ zpowers z))
    {E : Subgroup (alternatingGroup (Fin 5))} (hE : Nat.card E = 4) :
    (∀ s ∈ C.fixS hS E, s * s = 1) ∧ (∀ s ∈ C.fixS hS E, ∀ s' ∈ C.fixS hS E, s * s' = s' * s) ∧
      Nat.card (C.fixS hS E) = 16 ∧ Nat.card (C.fixS hS E ⊓ hS.Wt t : Subgroup G) = 8 := by
  obtain ⟨w₀, hw₀W, hw₀F, hw₀Z, hw₀sq, hval⟩ := C.exists_w₀ hS hHS hx ht hzZ hz1 hz hE
  have hw₀S := hw₀W.1
  obtain ⟨w₁, hw₁def⟩ : ∃ w₁, w₁ = x * w₀ * x⁻¹ := ⟨_, rfl⟩
  have hw₁S : w₁ ∈ S := hw₁def ▸ (mem_normalizer_iff.mp hx.normS w₀).mp hw₀S
  have hw₁F : w₁ ∈ C.fixS hS E := hw₁def ▸ C.conj_x_mem_fixS hS hHS hx hxH hxH' hw₀F
  have hw₁sq : w₁ * w₁ = 1 := by
    calc w₁ * w₁ = x * (w₀ * w₀) * x⁻¹ := by rw [hw₁def]; group
      _ = 1 := by rw [hw₀sq]; group
  have hc01 : Commute w₀ w₁ := by
    rw [hw₁def]
    exact C.comm_conj_x_eq hS hx ht hzZ hz1 hz hw₀W hw₀sq
  have hΨ0 : C.Ψ w₀ ≠ 0 := fun h => hw₀Z ((C.Ψ_eq_zero_iff hS hw₀S).mp h)
  have hΨ1 : C.Ψ w₁ ≠ 0 := by
    intro h
    apply hw₀Z
    have h1 : w₁ ∈ Z := (C.Ψ_eq_zero_iff hS hw₁S).mp h
    have h2 := (mem_normalizer_iff.mp (inv_mem hx.normZ) w₁).mp h1
    have e : x⁻¹ * w₁ * x⁻¹⁻¹ = w₀ := by rw [hw₁def]; group
    rwa [e] at h2
  have hΨ01 : C.Ψ w₀ ≠ C.Ψ w₁ := by
    intro h
    apply hw₀Z
    have h1 : w₁ * w₀⁻¹ ∈ Z := (C.Ψ_eq_iff hS hw₁S hw₀S).mp h.symm
    have hw₁W : w₁ ∈ hS.Wt t := by
      have e : w₁ = (w₁ * w₀⁻¹) * w₀ := by group
      rw [e]
      exact (hS.Wt t).mul_mem (hS.Z_le_Wt ht.normS h1) hw₀W
    rw [hw₁def] at hw₁W
    exact C.mem_Z_of_conj_mem_Wt hS hx ht hw₀W hw₁W
  obtain ⟨e, he⟩ : ∃ e : Bool × Bool → G,
      ∀ p, e p = (if p.1 then w₀ else 1) * (if p.2 then w₁ else 1) := ⟨_, fun _ => rfl⟩
  have hite0 : ∀ i : Bool, (if i then w₀ else 1) ∈ C.fixS hS E := fun i => by
    cases i
    · exact one_mem _
    · exact hw₀F
  have hite1 : ∀ i : Bool, (if i then w₁ else 1) ∈ C.fixS hS E := fun i => by
    cases i
    · exact one_mem _
    · exact hw₁F
  have heF : ∀ p, e p ∈ C.fixS hS E := fun p => by
    rw [he]
    exact (C.fixS hS E).mul_mem (hite0 _) (hite1 _)
  have heΨ : ∀ p, C.Ψ (e p) = (if p.1 then C.Ψ w₀ else 0) + (if p.2 then C.Ψ w₁ else 0) := by
    rintro ⟨i, j⟩
    rw [he, C.Ψ_mul hS (hite0 i).1 (hite1 j).1]
    cases i <;> cases j <;> simp only [Bool.false_eq_true, ↓reduceIte, C.Ψ_one]
  have hcomm_ite : ∀ (a b : G), Commute a b → ∀ i j : Bool,
      Commute (if i then a else 1) (if j then b else 1) := by
    intro a b hab i j
    cases i <;> cases j <;> simp only [Bool.false_eq_true, ↓reduceIte, Commute.one_left,
      Commute.one_right, hab]
  have he_sq : ∀ p, e p * e p = 1 := by
    rintro ⟨i, j⟩
    rw [he]
    have hA : (if i then w₀ else 1) * (if i then w₀ else 1) = 1 := by
      cases i <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one, hw₀sq]
    have hB : (if j then w₁ else 1) * (if j then w₁ else 1) = 1 := by
      cases j <;> simp only [Bool.false_eq_true, ↓reduceIte, mul_one, hw₁sq]
    dsimp only
    rw [(hcomm_ite w₁ w₀ hc01.symm j i).mul_mul_mul_comm, hA, hB, one_mul]
  have he_comm : ∀ p p', Commute (e p) (e p') := by
    rintro ⟨i, j⟩ ⟨k, l⟩
    rw [he, he]
    dsimp only
    exact Commute.mul_left
      (Commute.mul_right (hcomm_ite w₀ w₀ (Commute.refl w₀) i k) (hcomm_ite w₀ w₁ hc01 i l))
      (Commute.mul_right (hcomm_ite w₁ w₀ hc01.symm j k) (hcomm_ite w₁ w₁ (Commute.refl w₁) j l))
  have hginj : Function.Injective (fun p : Bool × Bool =>
      (⟨C.Ψ (e p), C.Ψ_mem_img hS (heF p) (heF p).1⟩ : C.img hS (C.fixS hS E))) := by
    intro p p' h
    have h' := congrArg Subtype.val h
    simp only [heΨ] at h'
    exact inj_pair2 hΨ0 hΨ1 hΨ01 h'
  have hcard4 : Nat.card (Bool × Bool) = 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hgbij := hginj.bijective_of_nat_card_le (by rw [hcard4]; exact C.card_img_fixS_le hS hE)
  have hrep : ∀ s ∈ C.fixS hS E, ∃ p, C.Ψ s = C.Ψ (e p) := by
    intro s hs
    obtain ⟨p, hp⟩ := hgbij.2 ⟨C.Ψ s, C.Ψ_mem_img hS hs hs.1⟩
    exact ⟨p, (congrArg Subtype.val hp).symm⟩
  refine ⟨fun s hs => ?_, fun s hs s' hs' => ?_, ?_, ?_⟩
  · obtain ⟨p, hp⟩ := hrep s hs
    rw [C.sq_eq_of_Ψ_eq hS hs.1 (heF p).1 hp, he_sq]
  · obtain ⟨p, hp⟩ := hrep s hs
    obtain ⟨p', hp'⟩ := hrep s' hs'
    have h1 := C.comm_eq_of_Ψ_eq hS hs.1 (heF p).1 hs'.1 (heF p').1 hp hp'
    have h2 : e p * e p' * (e p)⁻¹ * (e p')⁻¹ = 1 := by
      rw [(he_comm p p').eq]
      group
    calc s * s' = (s * s' * s⁻¹ * s'⁻¹) * s' * s := by group
      _ = s' * s := by rw [h1, h2, one_mul]
  · have h1 := C.card_eq_four_mul hS (C.Z_le_fixS hS E) (fun s hs => hs.1)
    rw [h1, ← Nat.card_congr (Equiv.ofBijective _ hgbij), hcard4]
  · have hZ : Z ≤ C.fixS hS E ⊓ hS.Wt t := le_inf (C.Z_le_fixS hS E) (hS.Z_le_Wt ht.normS)
    have h1 := C.card_eq_four_mul hS hZ (inf_le_left.trans fun s hs => hs.1)
    have hw₀mem : C.Ψ w₀ ∈ C.img hS (C.fixS hS E ⊓ hS.Wt t) :=
      C.Ψ_mem_img hS ⟨hw₀F, hw₀W⟩ hw₀S
    have h2 : Nat.card (C.img hS (C.fixS hS E ⊓ hS.Wt t)) = 2 := by
      apply le_antisymm
      · refine card_le_two_of_forall (m₀ := C.Ψ w₀) ?_
        rintro _ ⟨s, hs, rfl⟩
        exact hval s hs.1
      · have hf : Function.Injective (fun b : Bool =>
            if b then (⟨C.Ψ w₀, hw₀mem⟩ : C.img hS (C.fixS hS E ⊓ hS.Wt t)) else 0) := by
          intro b b' h
          cases b <;> cases b'
          · rfl
          · exfalso
            have h' := congrArg Subtype.val h
            exact hΨ0 h'.symm
          · exfalso
            have h' := congrArg Subtype.val h
            exact hΨ0 h'
          · rfl
        have := Nat.card_le_card_of_injective _ hf
        rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
    rw [h1, h2]

end Sec2

end CFSG.ComponentClassification.AS81
