module

public import CFSG.LargeExtraspecial.S111BTI
public import CFSG.LargeExtraspecial.S111TZStar
public import CFSG.LargeExtraspecial.S111TNoOdd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4

theorem odd_card_oddCore_of_finite (Y : Type*) [Group Y] [Finite Y] :
    Odd (Nat.card (CFSG.oddCore Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem conj_mem_oddCore {H : Type*} [Group H] [Finite H] {Y : Subgroup H} {s : H}
    (hs : ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) (hs' : ∀ y ∈ Y, s⁻¹ * y * s ∈ Y) {x : H}
    (hx : x ∈ (CFSG.oddCore Y).map Y.subtype) :
    s * x * s⁻¹ ∈ (CFSG.oddCore Y).map Y.subtype := by
  set K := (CFSG.oddCore Y).map Y.subtype with hK
  set K' := K.map (MulAut.conj s).toMonoidHom with hK'
  have hKY : K ≤ Y := map_subtype_le _
  have hKn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    rintro y hy _ ⟨k, hk, rfl⟩
    exact ⟨⟨y, hy⟩ * k * ⟨y, hy⟩⁻¹, (CFSG.oddCore_normal Y).conj_mem k hk _, rfl⟩
  have hK'Y : K' ≤ Y := by
    rintro _ ⟨k, hk, rfl⟩
    exact hs _ (hKY hk)
  have hN : (K'.subgroupOf Y).Normal := ⟨fun n hn y => by
    rw [mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := hn
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hkn
    refine ⟨(s⁻¹ * y * s) * k * (s⁻¹ * y * s)⁻¹, hKn _ (hs' _ y.2) k hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    rw [← hkn]
    group⟩
  have hodd : Odd (Nat.card (K'.subgroupOf Y)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'Y).toEquiv, hK',
      Subgroup.card_map_of_injective (MulAut.conj s).injective, hK,
      Subgroup.card_map_of_injective Y.subtype_injective]
    exact odd_card_oddCore_of_finite Y
  have hle : K'.subgroupOf Y ≤ CFSG.oddCore Y := le_sSup ⟨hN, hodd⟩
  have hx' : s * x * s⁻¹ ∈ K' := ⟨x, hx, rfl⟩
  exact ⟨⟨_, hK'Y hx'⟩, hle (mem_subgroupOf.mpr hx'), rfl⟩

variable {G : Type*} [Group G] [Finite G]

variable (S : Setting G) in
noncomputable abbrev Ybar111 (k k' : G) : Subgroup S.O :=
  (S.Lbar k ⊔ S.Lbar k') ⊓ centralizer ((Ebar S k k' ⊔ Ebar S k' k : Subgroup S.O) : Set S.O)

variable {S : Setting G} {g : G} {A : Subgroup G} {h k k' : G}

theorem Cfg111.exists_eq_Lbar_of_inf_ne_bot (C : Cfg111 S g A) (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) {x : S.O} (hx : x ∈ S.Mbar)
    (hne : S.Lbar k ⊓ (S.Lbar k).map (MulAut.conj x).toMonoidHom ≠ ⊥) :
    ∃ j : G, j * S.z * j⁻¹ ∈ A ∧ j * S.z * j⁻¹ ≠ S.z ∧
      (S.Lbar k).map (MulAut.conj x).toMonoidHom = S.Lbar j := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [← Lbar_mul S m k] at hne ⊢
  have hkQ := C.inc.le_QG hk
  exact ⟨(m : G) * k, C.mem_of_Lbar_inf_ne_bot hk hkz (conj_mem_QG' S m.2 hkQ)
    (conj_ne_z' S m.2 hkz) hne, conj_ne_z' S m.2 hkz, rfl⟩

theorem IncClosed.exists_comm_apply (hA : IncClosed S A) (hk : k * S.z * k⁻¹ ∈ A)
    (hkz : k * S.z * k⁻¹ ≠ S.z) {j : G} (hj : j * S.z * j⁻¹ ∈ A) (hjz : j * S.z * j⁻¹ ≠ S.z)
    (hcl : S.cl (j * S.z * j⁻¹) ≠ S.cl (k * S.z * k⁻¹)) :
    ∃ x₀ ∈ S.Lbar k, ∃ y₀ ∈ S.Lbar j,
      ((x₀ * y₀ * x₀⁻¹ * y₀⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) =
        S.cl (k * S.z * k⁻¹) + S.cl (j * S.z * j⁻¹) := by
  have hkQ := hA.le_QG hk
  have hjQ := hA.le_QG hj
  have ha0 := cl_conj_z_ne_zero S hkQ hkz
  have ha'0 := cl_conj_z_ne_zero S hjQ hjz
  have haA := S.cl_mem_clSub hk hkQ
  have ha'A := S.cl_mem_clSub hj hjQ
  obtain ⟨f, hfa', hfp⟩ := exists_form_eq_one (p := (ZMod 2) ∙ S.cl (k * S.z * k⁻¹))
    (x := S.cl (j * S.z * j⁻¹)) (by
      rw [mem_span_cl_iff]
      rintro (e | e)
      · exact ha'0 e
      · exact hcl e)
  have hfa := hfp _ (Submodule.mem_span_singleton_self _)
  obtain ⟨f', hf'a, hf'p⟩ := exists_form_eq_one (p := (ZMod 2) ∙ S.cl (j * S.z * j⁻¹))
    (x := S.cl (k * S.z * k⁻¹)) (by
      rw [mem_span_cl_iff]
      rintro (e | e)
      · exact ha0 e
      · exact hcl e.symm)
  have hf'a' := hf'p _ (Submodule.mem_span_singleton_self _)
  obtain ⟨x₀, hx₀, hx₀v⟩ := hA.exists_mem_Lbar hk hkz f hfa
  obtain ⟨y₀, hy₀, hy₀v⟩ := hA.exists_mem_Lbar hj hjz f' hf'a'
  refine ⟨x₀, hx₀, y₀, hy₀, ?_⟩
  have e1 : (y₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹)) =
      S.cl (k * S.z * k⁻¹) + S.cl (j * S.z * j⁻¹) := by
    rw [hy₀v _ haA, hf'a, one_smul]
  have e2 : (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k * S.z * k⁻¹) + S.cl (j * S.z * j⁻¹)) =
      S.cl (j * S.z * j⁻¹) := by
    rw [hx₀v _ (Submodule.add_mem _ haA ha'A), map_add, hfa, hfa', zero_add, one_smul,
      add_comm (S.cl (k * S.z * k⁻¹)), add_assoc, ZModModule.add_self, add_zero]
  have e3 : (y₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (j * S.z * j⁻¹)) = S.cl (j * S.z * j⁻¹) := by
    rw [hy₀v _ ha'A, hf'a', zero_smul, add_zero]
  have e4 : (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (j * S.z * j⁻¹)) =
      S.cl (j * S.z * j⁻¹) + S.cl (k * S.z * k⁻¹) := by
    rw [hx₀v _ ha'A, hfa', one_smul]
  rw [inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S hkQ hx₀),
    inv_eq_of_mul_eq_one_right (mul_self_of_mem_Lbar S hjQ hy₀), coe_mul_apply, coe_mul_apply,
    coe_mul_apply, e1, e2, e3, e4, add_comm]

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem Ebar_le_normalizer : Ebar S k k' ≤ normalizer (Ebar S k' k : Set S.O) := fun e he =>
  mem_normalizer_of_conj_mem (fun f hf => by
    rw [P.commute_of_mem_Ebar he hf, mul_inv_cancel_right]; exact hf) (fun f hf => by
    rw [inv_inv, P.commute_of_mem_Ebar (inv_mem he) hf, inv_mul_cancel_right]; exact hf)

theorem EF_comm {a b : S.O} (ha : a ∈ Ebar S k k' ⊔ Ebar S k' k)
    (hb : b ∈ Ebar S k k' ⊔ Ebar S k' k) : a * b = b * a := by
  obtain ⟨e₁, he₁, f₁, hf₁, rfl⟩ := exists_mul_of_mem_sup P.Ebar_le_normalizer ha
  obtain ⟨e₂, he₂, f₂, hf₂, rfl⟩ := exists_mul_of_mem_sup P.Ebar_le_normalizer hb
  have h1 := P.commute_of_mem_Ebar he₂ hf₁
  have h2 := P.commute_of_mem_Ebar he₁ hf₂
  have h3 := Lbar_comm S P.memQ he₁.1 he₂.1
  have h4 := Lbar_comm S P.memQ' hf₁.1 hf₂.1
  calc e₁ * f₁ * (e₂ * f₂) = e₁ * (f₁ * e₂) * f₂ := by group
    _ = e₁ * e₂ * (f₁ * f₂) := by rw [← h1]; group
    _ = e₂ * e₁ * (f₂ * f₁) := by rw [h3, h4]
    _ = e₂ * (e₁ * f₂) * f₁ := by group
    _ = e₂ * f₂ * (e₁ * f₁) := by rw [h2]; group

theorem comm_mem_Ebar_of_mem_EF {l n : S.O} (hl : l ∈ S.Lbar k)
    (hn : n ∈ Ebar S k k' ⊔ Ebar S k' k) : l * n * l⁻¹ * n⁻¹ ∈ Ebar S k k' := by
  obtain ⟨e, he, f, hf, rfl⟩ := exists_mul_of_mem_sup P.Ebar_le_normalizer hn
  have h1 := P.comm_mem_Ebar hl hf
  have hle : l * e = e * l := Lbar_comm S P.memQ hl he.1
  have hce : e * (l * f * l⁻¹ * f⁻¹) = (l * f * l⁻¹ * f⁻¹) * e := Lbar_comm S P.memQ he.1 h1.1
  have e2 : l * (e * f) * l⁻¹ * (e * f)⁻¹ = e * (l * f * l⁻¹ * f⁻¹) * e⁻¹ := by
    calc l * (e * f) * l⁻¹ * (e * f)⁻¹ = (l * e) * f * l⁻¹ * f⁻¹ * e⁻¹ := by group
      _ = e * (l * f * l⁻¹ * f⁻¹) * e⁻¹ := by rw [hle]; group
  rw [e2, hce, mul_inv_cancel_right]
  exact h1

theorem Ebar_ne_bot' (hE : Ebar S k k' ≠ ⊥) : Ebar S k' k ≠ ⊥ := by
  intro h0
  apply hE
  have h1 := P.card_Ebar_eq
  rw [h0, Subgroup.card_bot] at h1
  exact Subgroup.eq_bot_of_card_eq _ h1

theorem mem_of_commute (hE : Ebar S k k' ≠ ⊥) {l : S.O} (hl : l ∈ S.Lbar k)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * l = l * n) :
    l ∈ Ebar S k k' ⊔ Ebar S k' k := by
  by_cases hlE : l ∈ Ebar S k k'
  · exact mem_sup_left hlE
  exfalso
  obtain ⟨⟨f, hf⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (P.Ebar_ne_bot' hE)
  exact hf1 (Subtype.ext (P.eq_one_of_commute hl hlE hf (hc f (mem_sup_right hf)).symm))

theorem zHyp (hE : Ebar S k k' ≠ ⊥) :
    ZHyp (S.Lbar k ⊔ S.Lbar k') (Ebar S k k' ⊔ Ebar S k' k) (S.Lbar k) where
  NX := Ebar_sup_le S k k'
  LX := le_sup_left
  Nn := fun _ hx _ hn => P.conj_mem_EF hx hn
  N2 := P.isPGroup_EF
  Nc := fun _ ha _ hb => P.EF_comm ha hb
  L2 := isPGroup_Lbar S P.memQ
  Li := fun _ hl => mul_self_of_mem_Lbar S P.memQ hl
  Lc := fun _ ha _ hb => Lbar_comm S P.memQ ha hb
  LN := fun _ hl hc => P.mem_of_commute hE hl hc
  wc := fun _ hx hc => P.map_conj_eq_of_conj_mem hx hc
  nc := fun _ hRX hR2 hLR => S4.le_normalizer_of_weaklyClosed P.hy.cons.weaklyClosed hR2
    (hRX.trans (Lbar_sup_le_Mbar S k k')) hLR

theorem map_Ebar_eq {x l : S.O} (hx : x ∈ S.Lbar k ⊔ S.Lbar k') (hl : l ∈ S.Lbar k)
    (hlE : l ∉ Ebar S k k')
    (hlx : l ∈ (S.Lbar k).map (MulAut.conj x).toMonoidHom ⊔ (Ebar S k k' ⊔ Ebar S k' k)) :
    (Ebar S k k').map (MulAut.conj x).toMonoidHom = Ebar S k k' := by
  have hLxN : (S.Lbar k).map (MulAut.conj x).toMonoidHom ≤
      normalizer ((Ebar S k k' ⊔ Ebar S k' k : Subgroup S.O) : Set S.O) := by
    rintro _ ⟨l₁, hl₁, rfl⟩
    exact P.le_normalizer_EF (mul_mem (mul_mem hx (mem_sup_left hl₁)) (inv_mem hx))
  obtain ⟨_, ⟨l₁, hl₁, rfl⟩, b, hb, hab⟩ := exists_mul_of_mem_sup hLxN hlx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hab
  have hle : (Ebar S k k').map (MulAut.conj x).toMonoidHom ≤ Ebar S k k' := by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hen : x * e * x⁻¹ ∈ Ebar S k k' ⊔ Ebar S k' k := P.conj_mem_EF hx (mem_sup_left he)
    have hc1 : x * e * x⁻¹ * (x * l₁ * x⁻¹) = (x * l₁ * x⁻¹) * (x * e * x⁻¹) := by
      have := Lbar_comm S P.memQ he.1 hl₁
      calc x * e * x⁻¹ * (x * l₁ * x⁻¹) = x * (e * l₁) * x⁻¹ := by group
        _ = x * (l₁ * e) * x⁻¹ := by rw [this]
        _ = (x * l₁ * x⁻¹) * (x * e * x⁻¹) := by group
    have hc2 := P.EF_comm hen hb
    have hcl : x * e * x⁻¹ * l = l * (x * e * x⁻¹) := by
      rw [← hab]
      calc x * e * x⁻¹ * (x * l₁ * x⁻¹ * b) = x * e * x⁻¹ * (x * l₁ * x⁻¹) * b := by group
        _ = (x * l₁ * x⁻¹) * (x * e * x⁻¹ * b) := by rw [hc1]; group
        _ = (x * l₁ * x⁻¹) * (b * (x * e * x⁻¹)) := by rw [hc2]
        _ = x * l₁ * x⁻¹ * b * (x * e * x⁻¹) := by group
    obtain ⟨e₁, he₁, f₁, hf₁, he₁f₁⟩ := exists_mul_of_mem_sup P.Ebar_le_normalizer hen
    have hle1 : l * e₁ = e₁ * l := Lbar_comm S P.memQ hl he₁.1
    rw [← he₁f₁] at hcl
    have hlf : l * f₁ = f₁ * l := by
      have h2 : e₁ * (f₁ * l) = e₁ * (l * f₁) := by
        calc e₁ * (f₁ * l) = e₁ * f₁ * l := by group
          _ = l * (e₁ * f₁) := hcl
          _ = l * e₁ * f₁ := by group
          _ = e₁ * (l * f₁) := by rw [hle1]; group
      exact (mul_left_cancel h2).symm
    rw [← he₁f₁, P.eq_one_of_commute hl hlE hf₁ hlf, mul_one]
    exact he₁
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj x).injective).ge

theorem comm_mem_centralizer {x : S.O} (hx : x ∈ S.Lbar k ⊔ S.Lbar k') {j : G}
    (hjQ : j * S.z * j⁻¹ ∈ S.QG) (hj : (S.Lbar k).map (MulAut.conj x).toMonoidHom = S.Lbar j)
    (hEx : (Ebar S k k').map (MulAut.conj x).toMonoidHom = Ebar S k k')
    {x₀ y₀ : S.O} (hx₀ : x₀ ∈ S.Lbar k) (hy₀ : y₀ ∈ S.Lbar j) :
    x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ∈
      centralizer ((Ebar S k k' ⊔ Ebar S k' k : Subgroup S.O) : Set S.O) := by
  have hEj : Ebar S k k' ≤ S.Lbar j := by
    rw [← hj, ← hEx]; exact map_mono inf_le_left
  have hLjN : ⁅S.Lbar j, Ebar S k k' ⊔ Ebar S k' k⁆ ≤ Ebar S k k' := by
    rw [commutator_le]
    intro a₁ ha₁ b hb
    rw [← hj] at ha₁
    obtain ⟨l₁, hl₁, rfl⟩ := ha₁
    have hb' : x⁻¹ * b * x⁻¹⁻¹ ∈ Ebar S k k' ⊔ Ebar S k' k := P.conj_mem_EF (inv_mem hx) hb
    have h1 := P.comm_mem_Ebar_of_mem_EF hl₁ hb'
    have h2 : x * (l₁ * (x⁻¹ * b * x⁻¹⁻¹) * l₁⁻¹ * (x⁻¹ * b * x⁻¹⁻¹)⁻¹) * x⁻¹ ∈
        Ebar S k k' := by
      rw [← hEx]; exact ⟨_, h1, rfl⟩
    rw [commutatorElement_def]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert h2 using 1
    group
  have hNL : ⁅Ebar S k k' ⊔ Ebar S k' k, S.Lbar k⁆ ≤ Ebar S k k' := by
    rw [commutator_le]
    intro b hb a₁ ha₁
    have := inv_mem (P.comm_mem_Ebar_of_mem_EF ha₁ hb)
    rw [commutatorElement_def]
    convert this using 1
    group
  have hEL : ⁅Ebar S k k', S.Lbar k⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr fun e he =>
      mem_centralizer_iff.mpr fun a₁ ha₁ => Lbar_comm S P.memQ ha₁ he.1
  have hELj : ⁅Ebar S k k', S.Lbar j⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr fun e he =>
      mem_centralizer_iff.mpr fun a₁ ha₁ => Lbar_comm S hjQ ha₁ (hEj he)
  have h1 : ⁅⁅S.Lbar j, Ebar S k k' ⊔ Ebar S k' k⁆, S.Lbar k⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hLjN le_rfl).trans hEL.le)
  have h2 : ⁅⁅Ebar S k k' ⊔ Ebar S k' k, S.Lbar k⁆, S.Lbar j⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono hNL le_rfl).trans hELj.le)
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  have hw : x₀ * y₀ * x₀⁻¹ * y₀⁻¹ ∈ ⁅S.Lbar k, S.Lbar j⁆ := by
    have := commutator_mem_commutator hx₀ hy₀
    rwa [commutatorElement_def] at this
  rw [mem_centralizer_iff]
  intro n hn
  have h4 := commutator_mem_commutator hw hn
  rw [h3, mem_bot, commutatorElement_def] at h4
  calc n * (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) =
      (x₀ * y₀ * x₀⁻¹ * y₀⁻¹ * n * (x₀ * y₀ * x₀⁻¹ * y₀⁻¹)⁻¹ * n⁻¹)⁻¹ *
        (x₀ * y₀ * x₀⁻¹ * y₀⁻¹) * n := by group
    _ = x₀ * y₀ * x₀⁻¹ * y₀⁻¹ * n := by rw [h4, inv_one, one_mul]

theorem exists_mem_Ybar (hE : Ebar S k k' ≠ ⊥) {x l : S.O} (hx : x ∈ S.Lbar k ⊔ S.Lbar k')
    (hLx : (S.Lbar k).map (MulAut.conj x).toMonoidHom ≠ S.Lbar k) (hl : l ∈ S.Lbar k)
    (hlE : l ∉ Ebar S k k')
    (hlx : l ∈ (S.Lbar k).map (MulAut.conj x).toMonoidHom ⊔ (Ebar S k k' ⊔ Ebar S k' k)) :
    ∃ w ∈ Ybar111 S k k', (S.Lbar k).map (MulAut.conj w).toMonoidHom ≠ S.Lbar k := by
  have hEx := P.map_Ebar_eq hx hl hlE hlx
  have hELx : Ebar S k k' ≤ (S.Lbar k).map (MulAut.conj x).toMonoidHom := by
    rw [← hEx]; exact map_mono inf_le_left
  have hne : S.Lbar k ⊓ (S.Lbar k).map (MulAut.conj x).toMonoidHom ≠ ⊥ := fun h0 =>
    hE (le_bot_iff.mp (h0 ▸ le_inf inf_le_left hELx))
  obtain ⟨j, hjA, hjz, hj⟩ := P.cfg.exists_eq_Lbar_of_inf_ne_bot P.mem P.ne
    (Lbar_sup_le_Mbar S k k' hx) hne
  have hjQ := P.cfg.inc.le_QG hjA
  have hjX : S.Lbar j ≤ S.Lbar k ⊔ S.Lbar k' := by
    rw [← hj]
    rintro _ ⟨l₁, hl₁, rfl⟩
    exact mul_mem (mul_mem hx (mem_sup_left hl₁)) (inv_mem hx)
  have hcl : S.cl (j * S.z * j⁻¹) ≠ S.cl (k * S.z * k⁻¹) := fun e =>
    hLx (by rw [hj]; exact Lbar_eq_of_cl_eq S P.memQ P.ne hjQ e)
  obtain ⟨x₀, hx₀, y₀, hy₀, hw⟩ := P.cfg.inc.exists_comm_apply P.mem P.ne hjA hjz hcl
  refine ⟨x₀ * y₀ * x₀⁻¹ * y₀⁻¹, mem_inf.mpr ⟨mul_mem (mul_mem (mul_mem (mem_sup_left hx₀)
    (hjX hy₀)) (inv_mem (mem_sup_left hx₀))) (inv_mem (hjX hy₀)),
    P.comm_mem_centralizer hx hjQ hj hEx hx₀ hy₀⟩, fun he => ?_⟩
  have hfix := fix_of_mem_normalizer P.hy.hyp4 (mem_normalizer_iff_map_conj_eq.mpr he)
  rw [hw] at hfix
  apply cl_conj_z_ne_zero S hjQ hjz
  have := congrArg (fun v => v - S.cl (k * S.z * k⁻¹)) hfix
  simpa using this

end Pair111

end CFSG.LargeExtraspecial.S11
