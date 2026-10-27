module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4e

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem conj_injective_of_center_eq_bot {G : Type*} [Group G] (h : center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h1 : t ∈ center G := by
    rw [mem_center_iff]
    intro g
    have h2 : t * g * t⁻¹ = g := by
      have := congrArg (fun φ : MulAut G => φ g) ht
      simpa [MulAut.conj_apply] using this
    calc g * t = t * g * t⁻¹ * t := by rw [h2]
      _ = t * g := by group
  rw [h, mem_bot] at h1
  exact h1

omit [Finite X] in
theorem eq_one_or_of_card_two {G : Type} [Group G] {H : Subgroup G} (h2 : Nat.card H = 2)
    {x y : G} (hx : x ∈ H) (hy : y ∈ H) (hx1 : x ≠ 1) : y = 1 ∨ y = x := by
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have hox : orderOf x = 2 := by
    have h1 : orderOf (⟨x, hx⟩ : H) ∣ 2 := h2 ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hz : zpowers x = H := by
    refine eq_of_le_of_card_ge ((zpowers_le).mpr hx) ?_
    rw [Nat.card_zpowers, hox, h2]
  rw [← hz] at hy
  exact eq_one_or_of_mem_zpowers hox hy

abbrev Jbar (h : Hyp52 X) : Type := ↥h.J ⧸ pPrimeCore 2 ↥h.J

abbrev Dbar (h : Hyp52 X) : Subgroup (Jbar h) :=
  (h.D.subgroupOf h.J).map (QuotientGroup.mk' (pPrimeCore 2 ↥h.J))

structure Ctx4 (X : Type) [Group X] [Finite X] where
  s : Setting X
  z : X
  u : X
  b : X
  r : X
  hzD : z ∈ s.h.D
  hzS : ∀ t ∈ s.h.S, t * z = z * t
  hzz : z * z = 1
  hz1 : z ≠ 1
  hzP : z ∉ s.h.P
  hu : u ∈ normalizer (s.h.S : Set X)
  hua : u⁻¹ * s.h.a * u = z
  huz : u⁻¹ * z * u = s.h.a
  huu : u * u ∈ s.h.S
  hbB0 : b ∈ B0 s.h s.y
  hbb : b * b = 1
  hb1 : b ≠ 1
  hba : b ≠ s.h.a
  hnaz : ∀ g : X, g⁻¹ * s.h.a * g ≠ s.h.a * z
  hrb : r * b = b * r
  hrab : r⁻¹ * (s.h.a * b) * r = z ∨ r⁻¹ * (s.h.a * b) * r = z * b
  hInn : innOf (Dbar s.h) ≤ rhoImg s.h.J (conjugate s.h.P u)
  he : ∀ σ ∈ innOf (Dbar s.h), σ * rhoE s.h.J (u⁻¹ * b * u) = rhoE s.h.J (u⁻¹ * b * u) * σ
  hZD : ∀ t ∈ Dbar s.h, t ∈ centralizer (Dbar s.h : Set (Jbar s.h)) →
    MulAut.conj t = 1 ∨ MulAut.conj t = rhoE s.h.J z
  hsq : ∃ t ∈ Dbar s.h, t * t ≠ 1 ∧ t * t ∈ centralizer (Dbar s.h : Set (Jbar s.h))
  hprod : ∀ t ∈ Dbar s.h, ∃ i ∈ Dbar s.h, ∃ j ∈ Dbar s.h, i * i = 1 ∧ j * j = 1 ∧ t = i * j
  hC4 : ∀ R : Subgroup (MulAut (Jbar s.h)), IsPGroup 2 R →
    R ≤ centralizer (innOf (Dbar s.h) : Set (MulAut (Jbar s.h))) → Nat.card R ≤ 4
  hJ8 : ∀ R : Subgroup (MulAut (Jbar s.h)), IsPGroup 2 R → innOf (Dbar s.h) ≤ R →
    ∀ E : Subgroup (MulAut (Jbar s.h)), E ≤ R → (∀ e ∈ E, e * e = 1) → Nat.card E = 8 →
      E ≤ innOf (Dbar s.h) ⊔ (R ⊓ centralizer (innOf (Dbar s.h) : Set (MulAut (Jbar s.h))))
  hRk : ∀ E : Subgroup (MulAut (Jbar s.h)), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 8

namespace Ctx4

variable (c : Ctx4 X)

abbrev P' : Subgroup X := conjugate c.s.h.P c.u

abbrev b' : X := c.u⁻¹ * c.b * c.u

noncomputable abbrev e : MulAut (Jbar c.s.h) := rhoE c.s.h.J c.b'

theorem b_mem_P : c.b ∈ c.s.h.P := c.s.h.B_le_P (c.s.B0_le_B c.hbB0)

theorem b_mem_S : c.b ∈ c.s.h.S := (mem_inf.mp c.b_mem_P).1

theorem z_mem_S : c.z ∈ c.s.h.S := c.s.h.D_le_S c.hzD

theorem mem_P'_of_mem_P {x : X} (hx : x ∈ c.s.h.P) : c.u⁻¹ * x * c.u ∈ c.P' := by
  rw [mem_conjugate_iff, show c.u * (c.u⁻¹ * x * c.u) * c.u⁻¹ = x by group]
  exact hx

theorem conj_mem_P' {x : X} (hx : x ∈ c.s.h.P) : c.u * x * c.u⁻¹ ∈ c.P' := by
  rw [mem_conjugate_iff, show c.u * (c.u * x * c.u⁻¹) * c.u⁻¹ =
    (c.u * c.u) * x * (c.u * c.u)⁻¹ by group]
  exact c.s.h.conj_mem_P c.huu hx

theorem mem_P_of_mem_P' {y : X} (hy : y ∈ c.P') : c.u * y * c.u⁻¹ ∈ c.s.h.P :=
  mem_conjugate_iff.mp hy

theorem z_mem_P' : c.z ∈ c.P' := c.hua ▸ c.mem_P'_of_mem_P c.s.h.a_mem_P

theorem b'_mem_P' : c.b' ∈ c.P' := c.mem_P'_of_mem_P c.b_mem_P

theorem P'_le_S : c.P' ≤ c.s.h.S := c.s.conjugate_P_le_S c.hu

theorem P'_le_N : c.P' ≤ normalizer (c.s.h.J : Set X) := c.s.conjugate_P_le_normalizer c.hu

theorem z_ne_a : c.z ≠ c.s.h.a := fun h => c.hzP (h ▸ c.s.h.a_mem_P)

theorem ua_ne : c.u⁻¹ * c.s.h.a * c.u ≠ c.s.h.a := by
  rw [c.hua]
  exact c.z_ne_a

theorem P_inf_P' : c.s.h.P ⊓ c.P' = ⊥ := c.s.P_inf_conjugate_eq_bot c.hu c.ua_ne

theorem P'_inf_K : c.P' ⊓ coreActionKernel c.s.h.J = ⊥ :=
  c.s.conjugate_P_inf_kernel c.hu c.ua_ne

theorem comm_P_P' {x y : X} (hx : x ∈ c.s.h.P) (hy : y ∈ c.P') : x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ c.s.h.P ⊓ c.P' := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
      exact mul_mem hx (c.s.h.conj_mem_P (c.P'_le_S hy) (inv_mem hx))
    · exact mul_mem (c.s.conj_mem_conjugate_P c.hu (mem_inf.mp hx).1 hy) (inv_mem hy)
  rw [c.P_inf_P', mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem rho_inj {x y : X} (hx : x ∈ c.P') (hy : y ∈ c.P')
    (h : rhoE c.s.h.J x = rhoE c.s.h.J y) : x = y := by
  have hxN := c.P'_le_N hx
  have hyN := c.P'_le_N hy
  have h1 : rhoE c.s.h.J (x * y⁻¹) = 1 := by
    rw [rhoE_mul hxN (inv_mem hyN), rhoE_inv hyN, h, mul_inv_cancel]
  rw [rhoE_eq_one_iff (mul_mem hxN (inv_mem hyN))] at h1
  have h2 : x * y⁻¹ ∈ c.P' ⊓ coreActionKernel c.s.h.J :=
    mem_inf.mpr ⟨mul_mem hx (inv_mem hy), h1⟩
  rw [c.P'_inf_K, mem_bot, mul_inv_eq_one] at h2
  exact h2

theorem rho_eq_one_iff {x : X} (hx : x ∈ c.s.h.S) : rhoE c.s.h.J x = 1 ↔ x ∈ c.s.h.P := by
  rw [rhoE_eq_one_iff (c.s.h.S_le_normalizer hx)]
  exact ⟨fun h => mem_inf.mpr ⟨hx, h⟩, fun h => (mem_inf.mp h).2⟩

theorem conj_injective : Function.Injective (MulAut.conj : Jbar c.s.h →* MulAut (Jbar c.s.h)) :=
  conj_injective_of_center_eq_bot c.s.hZJ

theorem rho_mem_innOf {d : X} (hd : d ∈ c.s.h.D) : rhoE c.s.h.J d ∈ innOf (Dbar c.s.h) := by
  rw [rhoE_of_mem_J (c.s.h.D_le_J hd)]
  exact mem_map_of_mem _ (mem_map_of_mem _ (mem_subgroupOf.mpr hd))

theorem isPGroup_rhoImg_P' : IsPGroup 2 (rhoImg c.s.h.J c.P') := by
  have hW2 : IsPGroup 2 c.P' := c.s.h.isPGroup_S.to_le c.P'_le_S
  exact (hW2.of_equiv (subgroupOfEquivOfLe c.P'_le_N).symm).map _

theorem b'_mul_b' : c.b' * c.b' = 1 := by
  rw [show c.b' * c.b' = c.u⁻¹ * (c.b * c.b) * c.u by group, c.hbb]
  group

theorem e_comm {σ : MulAut (Jbar c.s.h)} (hσ : σ ∈ innOf (Dbar c.s.h)) : σ * c.e = c.e * σ :=
  c.he σ hσ

theorem e_mul_e : c.e * c.e = 1 := by
  have hN := c.P'_le_N c.b'_mem_P'
  rw [← rhoE_mul hN hN, c.b'_mul_b', rhoE_one]

theorem e_ne_one : c.e ≠ 1 := by
  intro h
  have h1 := c.rho_inj c.b'_mem_P' (one_mem _) (h.trans (rhoE_one _).symm)
  apply c.hb1
  calc c.b = c.u * c.b' * c.u⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem rho_z_ne_one : rhoE c.s.h.J c.z ≠ 1 := fun h => c.hzP ((c.rho_eq_one_iff c.z_mem_S).mp h)

theorem rho_z_mul_rho_z : rhoE c.s.h.J c.z * rhoE c.s.h.J c.z = 1 := by
  have hN := c.P'_le_N c.z_mem_P'
  rw [← rhoE_mul hN hN, c.hzz, rhoE_one]

theorem e_ne_rho_z : c.e ≠ rhoE c.s.h.J c.z := by
  intro h
  have h1 := c.rho_inj c.b'_mem_P' c.z_mem_P' h
  apply c.hba
  calc c.b = c.u * c.b' * c.u⁻¹ := by group
    _ = c.u * (c.u⁻¹ * c.s.h.a * c.u) * c.u⁻¹ := by rw [h1, c.hua]
    _ = c.s.h.a := by group

theorem e_not_mem : c.e ∉ innOf (Dbar c.s.h) := by
  rintro ⟨t, ht, hte⟩
  have htC : t ∈ centralizer (Dbar c.s.h : Set (Jbar c.s.h)) := by
    rw [mem_centralizer_iff]
    intro w hw
    apply c.conj_injective
    rw [map_mul, map_mul, hte]
    exact c.e_comm (mem_map_of_mem _ hw)
  rcases c.hZD t ht htC with h | h
  · exact c.e_ne_one (hte ▸ h)
  · exact c.e_ne_rho_z (hte ▸ h)

theorem orderOf_e : orderOf c.e = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c.e_mul_e) c.e_ne_one

theorem orderOf_rho_z : orderOf (rhoE c.s.h.J c.z) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c.rho_z_mul_rho_z) c.rho_z_ne_one

theorem mem_zpowers_e {σ : MulAut (Jbar c.s.h)} (h : σ ∈ zpowers c.e) : σ = 1 ∨ σ = c.e :=
  eq_one_or_of_mem_zpowers c.orderOf_e h

theorem comm_inn_e {x y : MulAut (Jbar c.s.h)} (hx : x ∈ innOf (Dbar c.s.h))
    (hy : y ∈ zpowers c.e) : x * y = y * x := by
  rcases c.mem_zpowers_e hy with rfl | rfl
  · rw [mul_one, one_mul]
  · exact c.e_comm hx

theorem rho_z_comm {σ : MulAut (Jbar c.s.h)} (hσ : σ ∈ innOf (Dbar c.s.h)) :
    σ * rhoE c.s.h.J c.z = rhoE c.s.h.J c.z * σ := by
  obtain ⟨_, ⟨⟨t, htJ⟩, ht, rfl⟩, rfl⟩ := hσ
  rw [rhoE_of_mem_J (c.s.h.D_le_J c.hzD), ← map_mul, ← map_mul]
  congr 1
  change QuotientGroup.mk' (pPrimeCore 2 ↥c.s.h.J) ⟨t, htJ⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥c.s.h.J) ⟨c.z, c.s.h.D_le_J c.hzD⟩ =
    QuotientGroup.mk' (pPrimeCore 2 ↥c.s.h.J) ⟨c.z, c.s.h.D_le_J c.hzD⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥c.s.h.J) ⟨t, htJ⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (c.hzS t (c.s.h.D_le_S (mem_subgroupOf.mp ht)))

noncomputable abbrev W : Subgroup (MulAut (Jbar c.s.h)) := innOf (Dbar c.s.h) ⊔ zpowers c.e

theorem mem_W {σ : MulAut (Jbar c.s.h)} (hσ : σ ∈ c.W) :
    ∃ t ∈ Dbar c.s.h, σ = MulAut.conj t ∨ σ = MulAut.conj t * c.e := by
  obtain ⟨τ, hτ, κ, hκ, rfl⟩ := exists_mul_of_mem_sup (fun x hx y hy => c.comm_inn_e hx hy) hσ
  obtain ⟨t, ht, rfl⟩ := hτ
  refine ⟨t, ht, ?_⟩
  rcases c.mem_zpowers_e hκ with rfl | rfl
  · left
    rw [mul_one]
  · right
    rfl

theorem e_comm_W {σ : MulAut (Jbar c.s.h)} (hσ : σ ∈ c.W) : σ * c.e = c.e * σ := by
  obtain ⟨t, ht, h | h⟩ := c.mem_W hσ
  · rw [h]
    exact c.e_comm (mem_map_of_mem _ ht)
  · rw [h, ← mul_assoc c.e (MulAut.conj t) c.e, ← c.e_comm (mem_map_of_mem _ ht)]

theorem sq_of_mem_W {σ : MulAut (Jbar c.s.h)} (hσ : σ ∈ c.W)
    (hc : ∀ τ ∈ innOf (Dbar c.s.h), σ * σ * τ = τ * (σ * σ)) :
    σ * σ = 1 ∨ σ * σ = rhoE c.s.h.J c.z := by
  obtain ⟨t, ht, h⟩ := c.mem_W hσ
  have hsq : σ * σ = MulAut.conj (t * t) := by
    rcases h with h | h
    · rw [h, map_mul]
    · have hte := c.e_comm (mem_map_of_mem (MulAut.conj : Jbar c.s.h →* MulAut (Jbar c.s.h)) ht)
      rw [h, map_mul]
      calc MulAut.conj t * c.e * (MulAut.conj t * c.e) =
          MulAut.conj t * (c.e * MulAut.conj t) * c.e := by group
        _ = MulAut.conj t * (MulAut.conj t * c.e) * c.e := by rw [← hte]
        _ = MulAut.conj t * MulAut.conj t * (c.e * c.e) := by group
        _ = MulAut.conj t * MulAut.conj t := by rw [c.e_mul_e, mul_one]
  have htt : t * t ∈ centralizer (Dbar c.s.h : Set (Jbar c.s.h)) := by
    rw [mem_centralizer_iff]
    intro w hw
    apply c.conj_injective
    have h1 := (hc _ (mem_map_of_mem MulAut.conj hw)).symm
    rw [hsq] at h1
    calc MulAut.conj (w * (t * t)) = MulAut.conj w * MulAut.conj (t * t) := map_mul _ _ _
      _ = MulAut.conj (t * t) * MulAut.conj w := h1
      _ = MulAut.conj (t * t * w) := (map_mul _ _ _).symm
  rw [hsq]
  exact c.hZD _ (mul_mem ht ht) htt

theorem cent_le_W : rhoImg c.s.h.J c.P' ⊓
    centralizer (innOf (Dbar c.s.h) : Set (MulAut (Jbar c.s.h))) ≤ c.W := by
  set K := zpowers (rhoE c.s.h.J c.z) ⊔ zpowers c.e with hK
  have hcomm : ∀ x ∈ zpowers (rhoE c.s.h.J c.z), ∀ y ∈ zpowers c.e, x * y = y * x := by
    intro x hx y hy
    exact c.comm_inn_e (zpowers_le.mpr (c.rho_mem_innOf c.hzD) hx) hy
  have hKle : K ≤ rhoImg c.s.h.J c.P' ⊓
      centralizer (innOf (Dbar c.s.h) : Set (MulAut (Jbar c.s.h))) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> refine mem_inf.mpr ⟨?_, ?_⟩
    · exact rhoE_mem_rhoImg c.P'_le_N c.z_mem_P'
    · rw [mem_centralizer_iff]
      intro τ hτ
      exact c.rho_z_comm hτ
    · exact rhoE_mem_rhoImg c.P'_le_N c.b'_mem_P'
    · rw [mem_centralizer_iff]
      intro τ hτ
      exact c.e_comm hτ
  have hdisj : zpowers (rhoE c.s.h.J c.z) ⊓ zpowers c.e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_inf.mp hx
    rcases eq_one_or_of_mem_zpowers c.orderOf_rho_z hx1 with h | h
    · exact h ▸ one_mem _
    · rcases c.mem_zpowers_e hx2 with h' | h'
      · exact h' ▸ one_mem _
      · exact absurd (h'.symm.trans h) c.e_ne_rho_z
  have hcardK : Nat.card K = 4 := by
    rw [hK, card_sup_of_commute hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers,
      c.orderOf_rho_z, c.orderOf_e]
  have h4 := c.hC4 _ (c.isPGroup_rhoImg_P'.to_le inf_le_left) inf_le_right
  have heq := eq_of_le_of_card_ge hKle (by rw [hcardK]; exact h4)
  rw [← heq, hK]
  exact sup_le ((zpowers_le.mpr (c.rho_mem_innOf c.hzD)).trans le_sup_left) le_sup_right

theorem E8_le_W {E : Subgroup (MulAut (Jbar c.s.h))} (hE : E ≤ rhoImg c.s.h.J c.P')
    (hE2 : ∀ x ∈ E, x * x = 1) (h8 : Nat.card E = 8) : E ≤ c.W :=
  (c.hJ8 _ c.isPGroup_rhoImg_P' c.hInn E hE hE2 h8).trans (sup_le le_sup_left c.cent_le_W)

@[expose] def PW : Subgroup X where
  carrier := {x | x ∈ c.P' ∧ rhoE c.s.h.J x ∈ c.W}
  mul_mem' := by
    rintro x y ⟨hx, hxW⟩ ⟨hy, hyW⟩
    refine ⟨mul_mem hx hy, ?_⟩
    rw [rhoE_mul (c.P'_le_N hx) (c.P'_le_N hy)]
    exact mul_mem hxW hyW
  one_mem' := ⟨one_mem _, by rw [rhoE_one]; exact one_mem _⟩
  inv_mem' := by
    rintro x ⟨hx, hxW⟩
    refine ⟨inv_mem hx, ?_⟩
    rw [rhoE_inv (c.P'_le_N hx)]
    exact inv_mem hxW

theorem PW_le_P' : c.PW ≤ c.P' := fun _ hx => hx.1

theorem PW_comm_b' {x : X} (hx : x ∈ c.PW) : x * c.b' = c.b' * x := by
  apply c.rho_inj (mul_mem hx.1 c.b'_mem_P') (mul_mem c.b'_mem_P' hx.1)
  rw [rhoE_mul (c.P'_le_N hx.1) (c.P'_le_N c.b'_mem_P'),
    rhoE_mul (c.P'_le_N c.b'_mem_P') (c.P'_le_N hx.1)]
  exact c.e_comm_W hx.2

theorem PW_sq {x : X} (hx : x ∈ c.PW)
    (hc : ∀ τ ∈ innOf (Dbar c.s.h), rhoE c.s.h.J (x * x) * τ = τ * rhoE c.s.h.J (x * x)) :
    x * x = 1 ∨ x * x = c.z := by
  have hxN := c.P'_le_N hx.1
  have h1 := c.sq_of_mem_W hx.2 (by rw [← rhoE_mul hxN hxN]; exact hc)
  rw [← rhoE_mul hxN hxN] at h1
  rcases h1 with h | h
  · exact Or.inl (c.rho_inj (mul_mem hx.1 hx.1) (one_mem _) (h.trans (rhoE_one _).symm))
  · exact Or.inr (c.rho_inj (mul_mem hx.1 hx.1) c.z_mem_P' h)

theorem le_PW_of_E8 {E : Subgroup X} (hE : E ≤ c.P') (hE2 : ∀ x ∈ E, x * x = 1)
    (h8 : Nat.card E = 8) : E ≤ c.PW := by
  have hEN : E ≤ normalizer (c.s.h.J : Set X) := hE.trans c.P'_le_N
  have hEK : E ⊓ coreActionKernel c.s.h.J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← c.P'_inf_K]
    exact mem_inf.mpr ⟨hE (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  have hρE : rhoImg c.s.h.J E ≤ rhoImg c.s.h.J c.P' := map_mono (fun w hw => hE hw)
  have hρE2 : ∀ σ ∈ rhoImg c.s.h.J E, σ * σ = 1 := by
    intro σ hσ
    obtain ⟨x, hx, hxN, rfl⟩ := exists_of_mem_rhoImg hσ
    rw [← rhoE_mul hxN hxN, hE2 x hx, rhoE_one]
  have hcard : Nat.card (rhoImg c.s.h.J E) = 8 := by rw [card_rhoImg hEN hEK le_rfl, h8]
  have hW := c.E8_le_W hρE hρE2 hcard
  intro x hx
  exact ⟨hE hx, hW (rhoE_mem_rhoImg hEN hx)⟩

end Ctx4

end Seven

end CFSG.ComponentClassification.GSThmB
