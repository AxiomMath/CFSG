module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic
public import CFSG.Walter.J1Props.Janko
public import CFSG.Walter.J1Props.Elt

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2

open Subgroup CFSG.Walter CFSG.Walter.J1Props

structure JankoSetting (Γ : Type) [Group Γ] [Finite Γ] (f t r r₁ : Γ) (D E : Subgroup Γ) :
    Prop where
  f_central : f ∈ center Γ
  f_ord : orderOf f = 5
  t_ord : orderOf t = 2
  D_iso : Nonempty (↥D ≃* A5)
  D_cent : D ≤ centralizer ({t} : Set Γ)
  D_disj : Disjoint (zpowers f) D
  t_not_mem : t ∉ zpowers f ⊔ D
  cent_t : centralizer ({t} : Set Γ) = zpowers t ⊔ (zpowers f ⊔ D)
  E_card : Nat.card E = 8
  E_exp : ∀ x ∈ E, x * x = 1
  t_mem : t ∈ E
  r_norm : r ∈ normalizer (E : Set Γ)
  r₁_norm : r₁ ∈ normalizer (E : Set Γ)
  r_ord : orderOf r = 3
  r₁_ord : orderOf r₁ = 3
  trans : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 →
    ∃ y ∈ closure ({r, r₁} : Set Γ), y * e * y⁻¹ = e'

namespace JankoSetting

variable {Γ : Type} [Group Γ] [Finite Γ] {f t r r₁ : Γ} {D E : Subgroup Γ}
  (h : JankoSetting Γ f t r r₁ D E)

include h

theorem t_mul_t : t * t = 1 := by
  rw [← pow_two, ← h.t_ord, pow_orderOf_eq_one]

theorem f_comm (x : Γ) : x * f = f * x := mem_center_iff.1 h.f_central x

theorem zpow_comm (x : Γ) (k : ℤ) : x * f ^ k = f ^ k * x :=
  ((Commute.zpow_right (h.f_comm x : Commute x f) k)).eq

theorem comm_of_mem_zpowers {c : Γ} (hc : (t * c)⁻¹ * (c * t) ∈ zpowers f) : c * t = t * c := by
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hc
  have hct : c * t * c⁻¹ = t * f ^ j := by
    calc c * t * c⁻¹ = (t * c) * ((t * c)⁻¹ * (c * t)) * c⁻¹ := by group
      _ = t * (c * f ^ j * c⁻¹) := by rw [hj]; group
      _ = t * f ^ j := by rw [h.zpow_comm c j]; group
  have hsq : (t * f ^ j) * (t * f ^ j) = f ^ (2 * j) := by
    calc (t * f ^ j) * (t * f ^ j) = t * (f ^ j * t) * f ^ j := by group
      _ = t * (t * f ^ j) * f ^ j := by rw [← h.zpow_comm t j]
      _ = (t * t) * (f ^ j * f ^ j) := by group
      _ = f ^ (2 * j) := by rw [h.t_mul_t, one_mul, ← zpow_add]; ring_nf
  have h1 : (c * t * c⁻¹) * (c * t * c⁻¹) = 1 := by
    calc (c * t * c⁻¹) * (c * t * c⁻¹) = c * (t * t) * c⁻¹ := by group
      _ = 1 := by rw [h.t_mul_t]; group
  rw [hct, hsq] at h1
  have h2 : ((orderOf f : ℕ) : ℤ) ∣ 2 * j := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [h.f_ord] at h2
  have h3 : ((5 : ℕ) : ℤ) ∣ j := by push_cast at h2 ⊢; omega
  have hj1 : f ^ j = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, h.f_ord]; exact h3
  have h4 : c * t * c⁻¹ = t := by rw [hct, hj1, mul_one]
  calc c * t = (c * t * c⁻¹) * c := by group
    _ = t * c := by rw [h4]

theorem card_D : Nat.card D = 60 := by
  obtain ⟨e⟩ := h.D_iso
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem D_le_centralizer_f : D ≤ centralizer (zpowers f : Set Γ) := fun d _ =>
  mem_centralizer_iff.2 fun x hx => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
    exact (h.zpow_comm d k).symm

theorem card_fD : Nat.card (zpowers f ⊔ D : Subgroup Γ) = 300 := by
  have e := (mulEquivProdSup h.D_le_centralizer_f h.D_disj).toEquiv
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zpowers, h.f_ord, h.card_D]

theorem fD_le_cent_t : zpowers f ⊔ D ≤ centralizer ({t} : Set Γ) :=
  sup_le (by rw [zpowers_le]; exact mem_centralizer_singleton_iff.2 (h.f_comm t).symm) h.D_cent

theorem card_cent_t : Nat.card (centralizer ({t} : Set Γ)) = 600 := by
  have hle : zpowers f ⊔ D ≤ centralizer (zpowers t : Set Γ) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact (Commute.zpow_right
        (mem_centralizer_singleton_iff.1 (h.fD_le_cent_t hx) : Commute x t) k).eq.symm
  have hdisj : Disjoint (zpowers t) (zpowers f ⊔ D) := by
    rw [disjoint_iff_inf_le]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx1
    have := zpow_mod_orderOf t k
    rw [h.t_ord] at this
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [← this]; simp [h0]
    · exfalso; apply h.t_not_mem
      rw [← this] at hx2; simpa [h1] using hx2
  have e := (mulEquivProdSup hle hdisj).toEquiv
  rw [h.cent_t, ← Nat.card_congr e, Nat.card_prod, Nat.card_zpowers, h.t_ord, h.card_fD]

theorem E_comm {x y : Γ} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  have hxy := h.E_exp (x * y) (mul_mem hx hy)
  have e1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h.E_exp x hx)
  have e2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h.E_exp y hy)
  have e3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  rw [mul_inv_rev, e1, e2] at e3
  exact e3.symm

theorem E_le_cent_t : E ≤ centralizer ({t} : Set Γ) := fun _ hx =>
  mem_centralizer_singleton_iff.2 (h.E_comm hx h.t_mem)

theorem isPGroup_E : IsPGroup 2 E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 3) (by rw [h.E_card]; norm_num)

theorem t_ne_one : t ≠ 1 := by
  intro h1
  have := h.t_ord
  rw [h1, orderOf_one] at this
  omega

theorem card_le_eight {P : Subgroup Γ} (hP : IsPGroup 2 P) (hle : P ≤ centralizer ({t} : Set Γ)) :
    Nat.card P ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  have hd : Nat.card P ∣ 600 := h.card_cent_t ▸ Subgroup.card_dvd_of_le hle
  rw [hn] at hd ⊢
  by_contra hlt
  have hn4 : 4 ≤ n := by
    by_contra hn3
    have : n ≤ 3 := by omega
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 hn4
  have := h16.trans hd
  omega

theorem exists_sylow_eq_E : ∃ S : Sylow 2 Γ, (S : Subgroup Γ) = E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hES⟩ := h.isPGroup_E.exists_le_sylow
  refine ⟨S, ?_⟩
  have hSp : IsPGroup 2 (S : Subgroup Γ) := S.isPGroup'
  have htS : t ∈ (S : Subgroup Γ) := hES h.t_mem
  have : Nontrivial ↥(S : Subgroup Γ) :=
    ⟨⟨⟨t, htS⟩, 1, fun h1 => h.t_ne_one (congrArg Subtype.val h1)⟩⟩
  have hZnt := hSp.center_nontrivial
  have hZp : IsPGroup 2 ↥(center ↥(S : Subgroup Γ)) :=
    hSp.of_injective (center ↥(S : Subgroup Γ)).subtype (Subgroup.subtype_injective _)
  have hdvd : 2 ∣ Nat.card ↥(center ↥(S : Subgroup Γ)) := by
    rcases hZp.card_eq_or_dvd with h1 | h2
    · exfalso
      have : Subsingleton ↥(center ↥(S : Subgroup Γ)) := Nat.card_eq_one_iff_unique.1 h1 |>.1
      exact not_subsingleton _ this
    · exact h2
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  set t' : Γ := ((c : ↥(S : Subgroup Γ)) : Γ) with ht'
  have ht'S : t' ∈ (S : Subgroup Γ) := (c : ↥(S : Subgroup Γ)).2
  have ht'c : ∀ s ∈ (S : Subgroup Γ), s * t' = t' * s := fun s hs => by
    have := mem_center_iff.1 c.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have ht'ord : orderOf t' = 2 := by
    rw [ht', Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  have ht'1 : t' ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at ht'ord; omega
  set Cs : Subgroup Γ := (S : Subgroup Γ) ⊓ centralizer ({t} : Set Γ) with hCs
  have hCsp : IsPGroup 2 Cs := hSp.to_le (inf_le_left)
  have hCs8 := h.card_le_eight hCsp inf_le_right
  have hECs : E ≤ Cs := le_inf hES h.E_le_cent_t
  have hCsE : Cs = E := (eq_of_le_of_card_ge hECs (by rw [h.E_card]; exact hCs8)).symm
  have ht'E : t' ∈ E := by
    rw [← hCsE]
    exact ⟨ht'S, mem_centralizer_singleton_iff.2 (ht'c t htS).symm⟩
  obtain ⟨y, -, hyt⟩ := h.trans t h.t_mem h.t_ne_one t' ht'E ht'1
  set S' : Subgroup Γ := (S : Subgroup Γ).map (MulAut.conj y⁻¹).toMonoidHom with hS'
  have hS'le : S' ≤ centralizer ({t} : Set Γ) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hst := ht'c s hs
    have hyt' : y⁻¹ * t' * y = t := by rw [← hyt]; group
    show y⁻¹ * s * y⁻¹⁻¹ * t = t * (y⁻¹ * s * y⁻¹⁻¹)
    calc y⁻¹ * s * y⁻¹⁻¹ * t = y⁻¹ * s * (y * t * y⁻¹) * y := by group
      _ = y⁻¹ * (s * t') * y := by rw [hyt]; group
      _ = y⁻¹ * (t' * s) * y := by rw [hst]
      _ = (y⁻¹ * t' * y) * (y⁻¹ * s * y⁻¹⁻¹) := by group
      _ = t * (y⁻¹ * s * y⁻¹⁻¹) := by rw [hyt']
  have hcardS' : Nat.card S' = Nat.card (S : Subgroup Γ) :=
    Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hSp
  have hS'p : IsPGroup 2 S' := IsPGroup.of_card (n := n) (by rw [hcardS', hn])
  have h8 := h.card_le_eight hS'p hS'le
  rw [hcardS'] at h8
  exact (eq_of_le_of_card_ge hES (by rw [h.E_card]; exact h8)).symm

theorem normal_zpowers : (zpowers f).Normal := ⟨fun n hn g => by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
  have e : g * f ^ k * g⁻¹ = f ^ k := by rw [h.zpow_comm g k]; group
  rw [e]
  exact zpow_mem (mem_zpowers f) k⟩

omit h in
theorem exists_ne_two {A : Subgroup Γ} (hA : 2 < Nat.card A) (a : Γ) :
    ∃ x ∈ A, x ≠ 1 ∧ x ≠ a := by
  by_contra hcon
  push Not at hcon
  have hsub : (A : Set Γ) ⊆ {1, a} := fun x hx => by
    by_cases h1 : x = 1
    · exact Or.inl h1
    · exact Or.inr (hcon x hx h1)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, a} : Set Γ).ncard ≤ 2 :=
    (Set.ncard_insert_le _ _).trans (by simp [Set.ncard_singleton])
  have h3 : Nat.card A = (A : Set Γ).ncard := (Nat.card_coe_set_eq _)
  omega

theorem quot_index_ne_two [(zpowers f).Normal] (M : Subgroup (Γ ⧸ zpowers f)) :
    M.index ≠ 2 := by
  intro hM
  have hπ : Function.Surjective (QuotientGroup.mk' (zpowers f)) := QuotientGroup.mk'_surjective _
  set M' := M.comap (QuotientGroup.mk' (zpowers f)) with hM'def
  have hM' : M'.index = 2 := by rw [hM'def, Subgroup.index_comap_of_surjective M hπ]; exact hM
  have : M'.Normal := Subgroup.normal_of_index_eq_two hM'
  have hmem : ∀ g : Γ, orderOf g = 3 → g ∈ M' := fun g hg => by
    have h3 : g ^ 3 = 1 := hg ▸ pow_orderOf_eq_one g
    have h2 := Subgroup.sq_mem_of_index_two hM' (g ^ 2)
    have e : (g ^ 2) ^ 2 = g := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h3, one_mul]
    rwa [e] at h2
  have hcl : closure ({r, r₁} : Set Γ) ≤ M' := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact hmem _ h.r_ord
    · rw [Set.mem_singleton_iff.1 hx]; exact hmem _ h.r₁_ord
  obtain ⟨S0, hS0⟩ := h.exists_sylow_eq_E
  have hEnle : ¬ E ≤ M' := by
    intro hle
    have hd : M'.index ∣ (S0 : Subgroup Γ).index := by
      rw [hS0]; exact Subgroup.index_dvd_of_le hle
    have hnd := S0.not_dvd_index
    rw [hM'] at hd
    exact hnd hd
  obtain ⟨e, heE, heM⟩ : ∃ e ∈ E, e ∉ M' := by
    by_contra hcon
    push Not at hcon
    exact hEnle fun x hx => hcon x hx
  have he1 : e ≠ 1 := fun h1 => heM (h1 ▸ one_mem _)
  have hcard : 2 < Nat.card E := by rw [h.E_card]; norm_num
  obtain ⟨x, hxE, hx1, hxe⟩ := exists_ne_two hcard e
  obtain ⟨e', he'E, he'M, he'1⟩ : ∃ e' ∈ E, e' ∈ M' ∧ e' ≠ 1 := by
    by_cases hxM : x ∈ M'
    · exact ⟨x, hxE, hxM, hx1⟩
    · refine ⟨e * x, mul_mem heE hxE, ?_, ?_⟩
      · obtain ⟨a, ha⟩ := (Subgroup.index_eq_two_iff' (H := M')).1 hM'
        have h1 : a * e ∈ M' := by
          rcases ha e with ⟨h1, -⟩ | ⟨h2, -⟩
          · exact h1
          · exact absurd h2 heM
        have h2 : a * x ∈ M' := by
          rcases ha x with ⟨h1, -⟩ | ⟨h2, -⟩
          · exact h1
          · exact absurd h2 hxM
        have e1 : e⁻¹ = e := inv_eq_of_mul_eq_one_right (h.E_exp e heE)
        have : e * x = (a * e)⁻¹ * (a * x) := by
          rw [mul_inv_rev, e1]; group
        rw [this]
        exact mul_mem (inv_mem h1) h2
      · intro h1
        apply hxe
        have := h.E_exp e heE
        calc x = e⁻¹ * (e * x) := by group
          _ = e⁻¹ := by rw [h1, mul_one]
          _ = e := inv_eq_of_mul_eq_one_right this
  obtain ⟨y, hy, hyee⟩ := h.trans e heE he1 e' he'E he'1
  have hyM := hcl hy
  apply heM
  have : e = y⁻¹ * e' * y := by rw [← hyee]; group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hyM) he'M) hyM

theorem sylow_comm (Q : Sylow 2 Γ) {x y : Γ} (hx : x ∈ (Q : Subgroup Γ))
    (hy : y ∈ (Q : Subgroup Γ)) : x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S0, hS0⟩ := h.exists_sylow_eq_E
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ S0 Q
  have key : ∀ z ∈ (Q : Subgroup Γ), ∃ s ∈ E, z = g * s * g⁻¹ := fun z hz => by
    rw [← hg] at hz
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    exact ⟨s, hS0 ▸ hs, rfl⟩
  obtain ⟨s, hs, rfl⟩ := key x hx
  obtain ⟨s', hs', rfl⟩ := key y hy
  have hss := h.E_comm hs hs'
  calc g * s * g⁻¹ * (g * s' * g⁻¹) = g * (s * s') * g⁻¹ := by group
    _ = g * (s' * s) * g⁻¹ := by rw [hss]
    _ = g * s' * g⁻¹ * (g * s * g⁻¹) := by group

theorem quot_abelian_sylow [(zpowers f).Normal] :
    CFSG.Walter.HasAbelianSylowTwo (Γ ⧸ zpowers f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P
  obtain ⟨Q, rfl⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective (zpowers f)) 2 P
  refine ⟨⟨fun a b => ?_⟩⟩
  have ha : (a : Γ ⧸ zpowers f) ∈ (Q : Subgroup Γ).map (QuotientGroup.mk' (zpowers f)) := a.2
  have hb : (b : Γ ⧸ zpowers f) ∈ (Q : Subgroup Γ).map (QuotientGroup.mk' (zpowers f)) := b.2
  obtain ⟨a', ha', ha''⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b', hb', hb''⟩ := Subgroup.mem_map.1 hb
  apply Subtype.ext
  show (a : Γ ⧸ zpowers f) * b = b * a
  rw [← ha'', ← hb'', ← map_mul, ← map_mul, h.sylow_comm Q ha' hb']

omit [Finite Γ] h in
theorem mk_ne_one_of_not_mem [(zpowers f).Normal] {x : Γ} (hx : x ∉ zpowers f) :
    (QuotientGroup.mk x : Γ ⧸ zpowers f) ≠ 1 := fun h1 => hx ((QuotientGroup.eq_one_iff x).1 h1)

noncomputable def jankoHyp [(zpowers f).Normal] : JankoHyp₀ (Γ ⧸ zpowers f) where
  index_ne_two := h.quot_index_ne_two
  abelian_sylow := h.quot_abelian_sylow
  t := QuotientGroup.mk t
  orderOf_t := by
    have htz : t ∉ zpowers f := fun hm => h.t_not_mem (mem_sup_left hm)
    refine orderOf_eq_prime ?_ (mk_ne_one_of_not_mem htz)
    rw [← QuotientGroup.mk_pow, pow_two, h.t_mul_t, QuotientGroup.mk_one]
  F := D.map (QuotientGroup.mk' (zpowers f))
  le_centralizer := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff]
    show QuotientGroup.mk d * QuotientGroup.mk t = QuotientGroup.mk t * QuotientGroup.mk d
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (mem_centralizer_singleton_iff.1 (h.D_cent hd))
  t_not_mem := by
    rintro ⟨d, hd, hdt⟩
    apply h.t_not_mem
    have hz : d⁻¹ * t ∈ zpowers f := by
      have : (QuotientGroup.mk d : Γ ⧸ zpowers f) = QuotientGroup.mk t := hdt
      exact QuotientGroup.eq.1 this
    have e : t = d * (d⁻¹ * t) := by group
    rw [e]
    exact mul_mem (mem_sup_right hd) (mem_sup_left hz)
  centralizer_eq := by
    apply le_antisymm
    · intro x hx
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective x
      rw [mem_centralizer_singleton_iff] at hx
      have hz : (t * c)⁻¹ * (c * t) ∈ zpowers f := by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hx
        exact QuotientGroup.eq.1 hx.symm
      have hct := h.comm_of_mem_zpowers hz
      have hcc : c ∈ zpowers t ⊔ (zpowers f ⊔ D) :=
        h.cent_t ▸ mem_centralizer_singleton_iff.2 hct
      have hmap := Subgroup.mem_map_of_mem (QuotientGroup.mk' (zpowers f)) hcc
      rw [Subgroup.map_sup, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
      have hf1 : QuotientGroup.mk' (zpowers f) f = 1 := (QuotientGroup.eq_one_iff f).2
        (mem_zpowers f)
      rw [hf1, Subgroup.zpowers_one_eq_bot, bot_sup_eq] at hmap
      exact hmap
    · refine sup_le (by rw [zpowers_le]; exact mem_centralizer_singleton_iff.2 rfl) ?_
      rintro _ ⟨d, hd, rfl⟩
      rw [mem_centralizer_singleton_iff]
      show QuotientGroup.mk d * QuotientGroup.mk t = QuotientGroup.mk t * QuotientGroup.mk d
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (mem_centralizer_singleton_iff.1 (h.D_cent hd))
  iso := by
    have hinj : Function.Injective ((QuotientGroup.mk' (zpowers f)).comp D.subtype) := by
      rw [injective_iff_map_eq_one]
      intro d hd
      have hz : (d : Γ) ∈ zpowers f := (QuotientGroup.eq_one_iff (d : Γ)).1 hd
      have : (d : Γ) ∈ zpowers f ⊓ D := ⟨hz, d.2⟩
      rw [h.D_disj.eq_bot] at this
      exact Subtype.ext (mem_bot.1 this)
    have hrange : ((QuotientGroup.mk' (zpowers f)).comp D.subtype).range =
        D.map (QuotientGroup.mk' (zpowers f)) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact (MulEquiv.subgroupCongr hrange.symm).trans
      ((MonoidHom.ofInjective hinj).symm.trans h.D_iso.some)

theorem card_eq : Nat.card Γ = 877800 := by
  have := h.normal_zpowers
  obtain ⟨e⟩ := (h.jankoHyp).nonempty_mulEquiv_walterJ1
  have h1 : Nat.card (Γ ⧸ zpowers f) = 175560 := by
    rw [Nat.card_congr e.toEquiv]; exact card_walterJ1
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (zpowers f), h1, Nat.card_zpowers,
    h.f_ord]

end JankoSetting

end CFSG.EvenSporadicStandard.RuStd.S2
