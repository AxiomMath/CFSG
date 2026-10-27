module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4f

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X]

structure CtxB (X : Type) [Group X] [Finite X] where
  h : Hyp52 X
  hSa : IsSylowIn h.S (centralizer ({h.a} : Set X))
  hJn : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X)
  hC : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a
  hZJ : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥
  z : X
  u : X
  b : X
  r : X
  hzD : z ∈ h.D
  hzS : ∀ t ∈ h.S, t * z = z * t
  hzz : z * z = 1
  hz1 : z ≠ 1
  hzP : z ∉ h.P
  hu : u ∈ normalizer (h.S : Set X)
  hua : u⁻¹ * h.a * u = z
  huz : u⁻¹ * z * u = h.a
  huu : u * u ∈ h.S
  hbP : b ∈ h.P
  hbb : b * b = 1
  hb1 : b ≠ 1
  hba : b ≠ h.a
  hnaz : ∀ g : X, g⁻¹ * h.a * g ≠ h.a * z
  hrb : r * b = b * r
  hrab : r⁻¹ * (h.a * b) * r = z ∨ r⁻¹ * (h.a * b) * r = z * b
  hInn : innOf (Dbar h) ≤ rhoImg h.J (conjugate h.P u)
  he : ∀ σ ∈ innOf (Dbar h), σ * rhoE h.J (u⁻¹ * b * u) = rhoE h.J (u⁻¹ * b * u) * σ
  hZD : ∀ t ∈ Dbar h, t ∈ centralizer (Dbar h : Set (Jbar h)) →
    MulAut.conj t = 1 ∨ MulAut.conj t = rhoE h.J z
  hsq : ∃ t ∈ Dbar h, t * t ≠ 1 ∧ t * t ∈ centralizer (Dbar h : Set (Jbar h))
  hprod : ∀ t ∈ Dbar h, ∃ i ∈ Dbar h, ∃ j ∈ Dbar h, i * i = 1 ∧ j * j = 1 ∧ t = i * j
  hC4 : ∀ R : Subgroup (MulAut (Jbar h)), IsPGroup 2 R →
    R ≤ centralizer (innOf (Dbar h) : Set (MulAut (Jbar h))) → Nat.card R ≤ 4
  hJ8 : ∀ R : Subgroup (MulAut (Jbar h)), IsPGroup 2 R → innOf (Dbar h) ≤ R →
    ∀ E : Subgroup (MulAut (Jbar h)), E ≤ R → (∀ e ∈ E, e * e = 1) → Nat.card E = 8 →
      E ≤ innOf (Dbar h) ⊔ (R ⊓ centralizer (innOf (Dbar h) : Set (MulAut (Jbar h))))
  hRk : ∀ E : Subgroup (MulAut (Jbar h)), (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 8

namespace CtxB

variable (c : CtxB X)

abbrev P' : Subgroup X := conjugate c.h.P c.u

abbrev b' : X := c.u⁻¹ * c.b * c.u

noncomputable abbrev e : MulAut (Jbar c.h) := rhoE c.h.J c.b'

theorem b_mem_P : c.b ∈ c.h.P := c.hbP

theorem P'_le_S : c.P' ≤ c.h.S := by
  intro w hw
  rw [mem_conjugate_iff] at hw
  have := (mem_normalizer_iff.mp (inv_mem c.hu) _).mp ((mem_inf.mp hw).1)
  rwa [show c.u⁻¹ * (c.u * w * c.u⁻¹) * c.u⁻¹⁻¹ = w by group] at this

theorem conj_mem_P'_of_mem_S {t w : X} (ht : t ∈ c.h.S) (hw : w ∈ c.P') :
    t * w * t⁻¹ ∈ c.P' := by
  rw [mem_conjugate_iff] at hw ⊢
  have htg : c.u * t * c.u⁻¹ ∈ c.h.S := (mem_normalizer_iff.mp c.hu t).mp ht
  have := c.h.conj_mem_P htg hw
  rwa [show c.u * t * c.u⁻¹ * (c.u * w * c.u⁻¹) * (c.u * t * c.u⁻¹)⁻¹ =
    c.u * (t * w * t⁻¹) * c.u⁻¹ by group] at this

theorem P'_le_N : c.P' ≤ normalizer (c.h.J : Set X) := c.P'_le_S.trans c.h.S_le_normalizer

theorem b_mem_S : c.b ∈ c.h.S := (mem_inf.mp c.b_mem_P).1

theorem z_mem_S : c.z ∈ c.h.S := c.h.D_le_S c.hzD

theorem mem_P'_of_mem_P {x : X} (hx : x ∈ c.h.P) : c.u⁻¹ * x * c.u ∈ c.P' := by
  rw [mem_conjugate_iff, show c.u * (c.u⁻¹ * x * c.u) * c.u⁻¹ = x by group]
  exact hx

theorem conj_mem_P' {x : X} (hx : x ∈ c.h.P) : c.u * x * c.u⁻¹ ∈ c.P' := by
  rw [mem_conjugate_iff, show c.u * (c.u * x * c.u⁻¹) * c.u⁻¹ =
    (c.u * c.u) * x * (c.u * c.u)⁻¹ by group]
  exact c.h.conj_mem_P c.huu hx

theorem mem_P_of_mem_P' {y : X} (hy : y ∈ c.P') : c.u * y * c.u⁻¹ ∈ c.h.P :=
  mem_conjugate_iff.mp hy

theorem z_mem_P' : c.z ∈ c.P' := c.hua ▸ c.mem_P'_of_mem_P c.h.a_mem_P

theorem b'_mem_P' : c.b' ∈ c.P' := c.mem_P'_of_mem_P c.b_mem_P

theorem z_ne_a : c.z ≠ c.h.a := fun h => c.hzP (h ▸ c.h.a_mem_P)

theorem ua_ne : c.u⁻¹ * c.h.a * c.u ≠ c.h.a := by
  rw [c.hua]
  exact c.z_ne_a

theorem P_inf_P' : c.h.P ⊓ c.P' = ⊥ := by
  by_contra hne
  obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal c.h.isPGroup_S
    (inf_le_left.trans c.h.P_le_S)
    (fun t ht v hv => mem_inf.mpr ⟨c.h.conj_mem_P ht (mem_inf.mp hv).1,
      c.conj_mem_P'_of_mem_S ht (mem_inf.mp hv).2⟩) hne
  obtain ⟨hwP, hwg⟩ := mem_inf.mp hw
  have hPZ : ∀ v ∈ c.h.P, (∀ t ∈ c.h.S, t * v = v * t) → v ≠ 1 → v = c.h.a := by
    intro v hvP hvZ hv1
    have hv : v ∈ c.h.P ⊓ centralizer (c.h.S : Set X) :=
      mem_inf.mpr ⟨hvP, mem_centralizer_iff.mpr hvZ⟩
    rw [c.hC] at hv
    exact (eq_one_or_of_mem_zpowers c.h.orderOf_a hv).resolve_left hv1
  have hwa := hPZ w hwP hwZ hw1
  rw [mem_conjugate_iff] at hwg
  have hpZ : ∀ t ∈ c.h.S, t * (c.u * w * c.u⁻¹) = c.u * w * c.u⁻¹ * t := by
    intro t ht
    have htg : c.u⁻¹ * t * c.u ∈ c.h.S := by
      have := (mem_normalizer_iff.mp (inv_mem c.hu) t).mp ht
      rwa [inv_inv] at this
    have h1 := hwZ _ htg
    calc t * (c.u * w * c.u⁻¹) = c.u * ((c.u⁻¹ * t * c.u) * w) * c.u⁻¹ := by group
      _ = c.u * (w * (c.u⁻¹ * t * c.u)) * c.u⁻¹ := by rw [h1]
      _ = c.u * w * c.u⁻¹ * t := by group
  have hp1 : c.u * w * c.u⁻¹ ≠ 1 := fun h1 => hw1 (by
    calc w = c.u⁻¹ * (c.u * w * c.u⁻¹) * c.u := by group
      _ = 1 := by rw [h1]; group)
  have hpa := hPZ _ hwg hpZ hp1
  apply c.ua_ne
  calc c.u⁻¹ * c.h.a * c.u = c.u⁻¹ * (c.u * w * c.u⁻¹) * c.u := by rw [hpa]
    _ = w := by group
    _ = c.h.a := hwa

theorem P'_inf_K : c.P' ⊓ coreActionKernel c.h.J = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwg, hwK⟩ := mem_inf.mp hw
  have hwP : w ∈ c.h.P := mem_inf.mpr ⟨c.P'_le_S hwg, hwK⟩
  have := c.P_inf_P' ▸ mem_inf.mpr ⟨hwP, hwg⟩
  exact this

theorem comm_P_P' {x y : X} (hx : x ∈ c.h.P) (hy : y ∈ c.P') : x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ c.h.P ⊓ c.P' := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
      exact mul_mem hx (c.h.conj_mem_P (c.P'_le_S hy) (inv_mem hx))
    · exact mul_mem (c.conj_mem_P'_of_mem_S (mem_inf.mp hx).1 hy) (inv_mem hy)
  rw [c.P_inf_P', mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem rho_inj {x y : X} (hx : x ∈ c.P') (hy : y ∈ c.P')
    (h : rhoE c.h.J x = rhoE c.h.J y) : x = y := by
  have hxN := c.P'_le_N hx
  have hyN := c.P'_le_N hy
  have h1 : rhoE c.h.J (x * y⁻¹) = 1 := by
    rw [rhoE_mul hxN (inv_mem hyN), rhoE_inv hyN, h, mul_inv_cancel]
  rw [rhoE_eq_one_iff (mul_mem hxN (inv_mem hyN))] at h1
  have h2 : x * y⁻¹ ∈ c.P' ⊓ coreActionKernel c.h.J :=
    mem_inf.mpr ⟨mul_mem hx (inv_mem hy), h1⟩
  rw [c.P'_inf_K, mem_bot, mul_inv_eq_one] at h2
  exact h2

theorem rho_eq_one_iff {x : X} (hx : x ∈ c.h.S) : rhoE c.h.J x = 1 ↔ x ∈ c.h.P := by
  rw [rhoE_eq_one_iff (c.h.S_le_normalizer hx)]
  exact ⟨fun h => mem_inf.mpr ⟨hx, h⟩, fun h => (mem_inf.mp h).2⟩

theorem conj_injective : Function.Injective (MulAut.conj : Jbar c.h →* MulAut (Jbar c.h)) :=
  conj_injective_of_center_eq_bot c.hZJ

theorem rho_mem_innOf {d : X} (hd : d ∈ c.h.D) : rhoE c.h.J d ∈ innOf (Dbar c.h) := by
  rw [rhoE_of_mem_J (c.h.D_le_J hd)]
  exact mem_map_of_mem _ (mem_map_of_mem _ (mem_subgroupOf.mpr hd))

theorem isPGroup_rhoImg_P' : IsPGroup 2 (rhoImg c.h.J c.P') := by
  have hW2 : IsPGroup 2 c.P' := c.h.isPGroup_S.to_le c.P'_le_S
  exact (hW2.of_equiv (subgroupOfEquivOfLe c.P'_le_N).symm).map _

theorem b'_mul_b' : c.b' * c.b' = 1 := by
  rw [show c.b' * c.b' = c.u⁻¹ * (c.b * c.b) * c.u by group, c.hbb]
  group

theorem e_comm {σ : MulAut (Jbar c.h)} (hσ : σ ∈ innOf (Dbar c.h)) : σ * c.e = c.e * σ :=
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

theorem rho_z_ne_one : rhoE c.h.J c.z ≠ 1 := fun h => c.hzP ((c.rho_eq_one_iff c.z_mem_S).mp h)

theorem rho_z_mul_rho_z : rhoE c.h.J c.z * rhoE c.h.J c.z = 1 := by
  have hN := c.P'_le_N c.z_mem_P'
  rw [← rhoE_mul hN hN, c.hzz, rhoE_one]

theorem e_ne_rho_z : c.e ≠ rhoE c.h.J c.z := by
  intro h
  have h1 := c.rho_inj c.b'_mem_P' c.z_mem_P' h
  apply c.hba
  calc c.b = c.u * c.b' * c.u⁻¹ := by group
    _ = c.u * (c.u⁻¹ * c.h.a * c.u) * c.u⁻¹ := by rw [h1, c.hua]
    _ = c.h.a := by group

theorem e_not_mem : c.e ∉ innOf (Dbar c.h) := by
  rintro ⟨t, ht, hte⟩
  have htC : t ∈ centralizer (Dbar c.h : Set (Jbar c.h)) := by
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

theorem orderOf_rho_z : orderOf (rhoE c.h.J c.z) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact c.rho_z_mul_rho_z) c.rho_z_ne_one

theorem mem_zpowers_e {σ : MulAut (Jbar c.h)} (h : σ ∈ zpowers c.e) : σ = 1 ∨ σ = c.e :=
  eq_one_or_of_mem_zpowers c.orderOf_e h

theorem comm_inn_e {x y : MulAut (Jbar c.h)} (hx : x ∈ innOf (Dbar c.h))
    (hy : y ∈ zpowers c.e) : x * y = y * x := by
  rcases c.mem_zpowers_e hy with rfl | rfl
  · rw [mul_one, one_mul]
  · exact c.e_comm hx

theorem rho_z_comm {σ : MulAut (Jbar c.h)} (hσ : σ ∈ innOf (Dbar c.h)) :
    σ * rhoE c.h.J c.z = rhoE c.h.J c.z * σ := by
  obtain ⟨_, ⟨⟨t, htJ⟩, ht, rfl⟩, rfl⟩ := hσ
  rw [rhoE_of_mem_J (c.h.D_le_J c.hzD), ← map_mul, ← map_mul]
  congr 1
  change QuotientGroup.mk' (pPrimeCore 2 ↥c.h.J) ⟨t, htJ⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥c.h.J) ⟨c.z, c.h.D_le_J c.hzD⟩ =
    QuotientGroup.mk' (pPrimeCore 2 ↥c.h.J) ⟨c.z, c.h.D_le_J c.hzD⟩ *
      QuotientGroup.mk' (pPrimeCore 2 ↥c.h.J) ⟨t, htJ⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (c.hzS t (c.h.D_le_S (mem_subgroupOf.mp ht)))

noncomputable abbrev W : Subgroup (MulAut (Jbar c.h)) := innOf (Dbar c.h) ⊔ zpowers c.e

theorem mem_W {σ : MulAut (Jbar c.h)} (hσ : σ ∈ c.W) :
    ∃ t ∈ Dbar c.h, σ = MulAut.conj t ∨ σ = MulAut.conj t * c.e := by
  obtain ⟨τ, hτ, κ, hκ, rfl⟩ := exists_mul_of_mem_sup (fun x hx y hy => c.comm_inn_e hx hy) hσ
  obtain ⟨t, ht, rfl⟩ := hτ
  refine ⟨t, ht, ?_⟩
  rcases c.mem_zpowers_e hκ with rfl | rfl
  · left
    rw [mul_one]
  · right
    rfl

theorem e_comm_W {σ : MulAut (Jbar c.h)} (hσ : σ ∈ c.W) : σ * c.e = c.e * σ := by
  obtain ⟨t, ht, h | h⟩ := c.mem_W hσ
  · rw [h]
    exact c.e_comm (mem_map_of_mem _ ht)
  · rw [h, ← mul_assoc c.e (MulAut.conj t) c.e, ← c.e_comm (mem_map_of_mem _ ht)]

theorem sq_of_mem_W {σ : MulAut (Jbar c.h)} (hσ : σ ∈ c.W)
    (hc : ∀ τ ∈ innOf (Dbar c.h), σ * σ * τ = τ * (σ * σ)) :
    σ * σ = 1 ∨ σ * σ = rhoE c.h.J c.z := by
  obtain ⟨t, ht, h⟩ := c.mem_W hσ
  have hsq : σ * σ = MulAut.conj (t * t) := by
    rcases h with h | h
    · rw [h, map_mul]
    · have hte := c.e_comm (mem_map_of_mem (MulAut.conj : Jbar c.h →* MulAut (Jbar c.h)) ht)
      rw [h, map_mul]
      calc MulAut.conj t * c.e * (MulAut.conj t * c.e) =
          MulAut.conj t * (c.e * MulAut.conj t) * c.e := by group
        _ = MulAut.conj t * (MulAut.conj t * c.e) * c.e := by rw [← hte]
        _ = MulAut.conj t * MulAut.conj t * (c.e * c.e) := by group
        _ = MulAut.conj t * MulAut.conj t := by rw [c.e_mul_e, mul_one]
  have htt : t * t ∈ centralizer (Dbar c.h : Set (Jbar c.h)) := by
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

theorem cent_le_W : rhoImg c.h.J c.P' ⊓
    centralizer (innOf (Dbar c.h) : Set (MulAut (Jbar c.h))) ≤ c.W := by
  set K := zpowers (rhoE c.h.J c.z) ⊔ zpowers c.e with hK
  have hcomm : ∀ x ∈ zpowers (rhoE c.h.J c.z), ∀ y ∈ zpowers c.e, x * y = y * x := by
    intro x hx y hy
    exact c.comm_inn_e (zpowers_le.mpr (c.rho_mem_innOf c.hzD) hx) hy
  have hKle : K ≤ rhoImg c.h.J c.P' ⊓
      centralizer (innOf (Dbar c.h) : Set (MulAut (Jbar c.h))) := by
    refine sup_le ?_ ?_ <;> rw [zpowers_le] <;> refine mem_inf.mpr ⟨?_, ?_⟩
    · exact rhoE_mem_rhoImg c.P'_le_N c.z_mem_P'
    · rw [mem_centralizer_iff]
      intro τ hτ
      exact c.rho_z_comm hτ
    · exact rhoE_mem_rhoImg c.P'_le_N c.b'_mem_P'
    · rw [mem_centralizer_iff]
      intro τ hτ
      exact c.e_comm hτ
  have hdisj : zpowers (rhoE c.h.J c.z) ⊓ zpowers c.e = ⊥ := by
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

theorem E8_le_W {E : Subgroup (MulAut (Jbar c.h))} (hE : E ≤ rhoImg c.h.J c.P')
    (hE2 : ∀ x ∈ E, x * x = 1) (h8 : Nat.card E = 8) : E ≤ c.W :=
  (c.hJ8 _ c.isPGroup_rhoImg_P' c.hInn E hE hE2 h8).trans (sup_le le_sup_left c.cent_le_W)

@[expose] def PW : Subgroup X where
  carrier := {x | x ∈ c.P' ∧ rhoE c.h.J x ∈ c.W}
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
    (hc : ∀ τ ∈ innOf (Dbar c.h), rhoE c.h.J (x * x) * τ = τ * rhoE c.h.J (x * x)) :
    x * x = 1 ∨ x * x = c.z := by
  have hxN := c.P'_le_N hx.1
  have h1 := c.sq_of_mem_W hx.2 (by rw [← rhoE_mul hxN hxN]; exact hc)
  rw [← rhoE_mul hxN hxN] at h1
  rcases h1 with h | h
  · exact Or.inl (c.rho_inj (mul_mem hx.1 hx.1) (one_mem _) (h.trans (rhoE_one _).symm))
  · exact Or.inr (c.rho_inj (mul_mem hx.1 hx.1) c.z_mem_P' h)

theorem le_PW_of_E8 {E : Subgroup X} (hE : E ≤ c.P') (hE2 : ∀ x ∈ E, x * x = 1)
    (h8 : Nat.card E = 8) : E ≤ c.PW := by
  have hEN : E ≤ normalizer (c.h.J : Set X) := hE.trans c.P'_le_N
  have hEK : E ⊓ coreActionKernel c.h.J = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [← c.P'_inf_K]
    exact mem_inf.mpr ⟨hE (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩
  have hρE : rhoImg c.h.J E ≤ rhoImg c.h.J c.P' := map_mono (fun w hw => hE hw)
  have hρE2 : ∀ σ ∈ rhoImg c.h.J E, σ * σ = 1 := by
    intro σ hσ
    obtain ⟨x, hx, hxN, rfl⟩ := exists_of_mem_rhoImg hσ
    rw [← rhoE_mul hxN hxN, hE2 x hx, rhoE_one]
  have hcard : Nat.card (rhoImg c.h.J E) = 8 := by rw [card_rhoImg hEN hEK le_rfl, h8]
  have hW := c.E8_le_W hρE hρE2 hcard
  intro x hx
  exact ⟨hE hx, hW (rhoE_mem_rhoImg hEN hx)⟩

end CtxB

end Eight2

end CFSG.ComponentClassification.GSThmB
