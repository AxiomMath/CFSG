module

public import CFSG.LocalAnalysis.EvenBN.Common.ProductSplitAmbient

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup
open scoped commutatorElement

section Factor

variable {G : Type*} [Group G] {S : Type*} [Group S] {N : Subgroup G} (ρ : N →* S × S)

@[expose] def prodFst : Subgroup G := ((MonoidHom.snd S S).comp ρ).ker.map N.subtype

theorem mem_prodFst_iff {g : G} : g ∈ prodFst ρ ↔ ∃ h : g ∈ N, (ρ ⟨g, h⟩).2 = 1 := by
  rw [prodFst, mem_map]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨h, h2⟩
    exact ⟨⟨g, h⟩, h2, rfl⟩

theorem prodFst_le : prodFst ρ ≤ N := map_subtype_le _

@[expose] def prodFstHom : prodFst ρ →* S :=
  (MonoidHom.fst S S).comp (ρ.comp (Subgroup.inclusion (prodFst_le ρ)))

theorem rho_inclusion_prodFst (x : prodFst ρ) :
    ρ (Subgroup.inclusion (prodFst_le ρ) x) = (prodFstHom ρ x, 1) := by
  refine Prod.ext rfl ?_
  obtain ⟨h, h2⟩ := (mem_prodFst_iff ρ).1 x.2
  exact h2

theorem conj_mem_prodFst {n g : G} (hn : n ∈ N) (hg : g ∈ prodFst ρ) :
    n * g * n⁻¹ ∈ prodFst ρ := by
  obtain ⟨hgN, hg2⟩ := (mem_prodFst_iff ρ).1 hg
  refine (mem_prodFst_iff ρ).2 ⟨mul_mem (mul_mem hn hgN) (inv_mem hn), ?_⟩
  have e : (⟨n * g * n⁻¹, mul_mem (mul_mem hn hgN) (inv_mem hn)⟩ : N) =
      ⟨n, hn⟩ * ⟨g, hgN⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, Prod.snd_mul, Prod.snd_mul, Prod.snd_inv, hg2]
  simp

variable {ρ}

theorem le_prodFst {X : Subgroup G} (hXN : X ≤ N) (hker : ρ.ker = X.subgroupOf N) :
    X ≤ prodFst ρ := by
  intro x hx
  refine (mem_prodFst_iff ρ).2 ⟨hXN hx, ?_⟩
  have h : (⟨x, hXN hx⟩ : N) ∈ ρ.ker := by
    rw [hker]
    exact mem_subgroupOf.2 hx
  rw [MonoidHom.mem_ker] at h
  rw [h]
  rfl

theorem surjective_prodFstHom (hρ : Function.Surjective ρ) :
    Function.Surjective (prodFstHom ρ) := by
  intro s
  obtain ⟨n, hn⟩ := hρ (s, 1)
  have hmem : (n : G) ∈ prodFst ρ := (mem_prodFst_iff ρ).2 ⟨n.2, congrArg Prod.snd hn⟩
  exact ⟨⟨n, hmem⟩, congrArg Prod.fst hn⟩

theorem ker_prodFstHom {X : Subgroup G} (hker : ρ.ker = X.subgroupOf N) :
    (prodFstHom ρ).ker = X.subgroupOf (prodFst ρ) := by
  ext x
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  have hx := rho_inclusion_prodFst ρ x
  have hiff : inclusion (prodFst_le ρ) x ∈ ρ.ker ↔ (x : G) ∈ X := by
    rw [hker, mem_subgroupOf]
    rfl
  rw [← hiff, MonoidHom.mem_ker, hx]
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    exact (Prod.ext_iff.1 h).1

variable (ρ) in
theorem le_normalizer_prodFst : N ≤ normalizer (prodFst ρ : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro g
  refine ⟨fun hg => conj_mem_prodFst ρ hn hg, fun hg => ?_⟩
  have := conj_mem_prodFst ρ (inv_mem hn) hg
  rwa [show n⁻¹ * (n * g * n⁻¹) * n⁻¹⁻¹ = g by group] at this

theorem le_normalizer_of_ker {X : Subgroup G} (hXN : X ≤ N) (hker : ρ.ker = X.subgroupOf N) :
    N ≤ normalizer (X : Set G) := by
  have : (X.subgroupOf N).Normal := by
    rw [← hker]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer hXN).1 this

theorem mem_iff_exists_prodFstHom {T : Subgroup G} {B : Subgroup S}
    (h : (T.subgroupOf N).map ρ = B.prod B) {b : S} :
    b ∈ B ↔ ∃ s : prodFst ρ, (s : G) ∈ T ∧ prodFstHom ρ s = b := by
  constructor
  · intro hb
    have hb' : (b, (1 : S)) ∈ (T.subgroupOf N).map ρ := by
      rw [h]
      exact mem_prod.2 ⟨hb, one_mem _⟩
    obtain ⟨s, hs, hρs⟩ := hb'
    have hsΛ : (s : G) ∈ prodFst ρ := (mem_prodFst_iff ρ).2 ⟨s.2, congrArg Prod.snd hρs⟩
    exact ⟨⟨s, hsΛ⟩, mem_subgroupOf.1 hs, congrArg Prod.fst hρs⟩
  · rintro ⟨s, hsT, rfl⟩
    have hs : ρ (inclusion (prodFst_le ρ) s) ∈ (T.subgroupOf N).map ρ :=
      ⟨_, mem_subgroupOf.2 hsT, rfl⟩
    rw [h, mem_prod] at hs
    exact hs.1

theorem prodFst_le_sup_map_conj {T X : Subgroup G} {B : Subgroup S} {r : G} {a : S}
    (hker : ρ.ker = X.subgroupOf N) (hXN : X ≤ N) (hXT : X ≤ T)
    (h : (T.subgroupOf N).map ρ = B.prod B) (hrN : r ∈ N) (hr : ρ ⟨r, hrN⟩ = (a, a))
    (hBa : B ⊔ B.map (MulAut.conj a).toMonoidHom = ⊤) :
    prodFst ρ ≤ (T ⊓ prodFst ρ) ⊔ (T ⊓ prodFst ρ).map (MulAut.conj r).toMonoidHom := by
  set Y : Subgroup G := T ⊓ prodFst ρ
  set W : Subgroup G := Y ⊔ Y.map (MulAut.conj r).toMonoidHom
  have hXY : X ≤ Y := le_inf hXT (le_prodFst hXN hker)
  have hYW : Y ≤ W := le_sup_left
  have hB : B ≤ (W.subgroupOf (prodFst ρ)).map (prodFstHom ρ) := by
    intro b hb
    obtain ⟨s, hsT, rfl⟩ := (mem_iff_exists_prodFstHom h).1 hb
    exact ⟨s, mem_subgroupOf.2 (hYW (mem_inf.2 ⟨hsT, s.2⟩)), rfl⟩
  have hBa' : B.map (MulAut.conj a).toMonoidHom ≤
      (W.subgroupOf (prodFst ρ)).map (prodFstHom ρ) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨s, hsT, rfl⟩ := (mem_iff_exists_prodFstHom h).1 hb
    have hs' : r * (s : G) * r⁻¹ ∈ prodFst ρ := conj_mem_prodFst ρ hrN s.2
    refine ⟨⟨r * s * r⁻¹, hs'⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      exact mem_sup_right ⟨s, mem_inf.2 ⟨hsT, s.2⟩, rfl⟩
    · have e : (⟨r * s * r⁻¹, prodFst_le ρ hs'⟩ : N) =
          ⟨r, hrN⟩ * inclusion (prodFst_le ρ) s * ⟨r, hrN⟩⁻¹ := rfl
      show (ρ ⟨r * s * r⁻¹, prodFst_le ρ hs'⟩).1 = a * (ρ (inclusion (prodFst_le ρ) s)).1 * a⁻¹
      rw [e, map_mul, map_mul, map_inv, hr]
      rfl
  have htop : (⊤ : Subgroup S) ≤ (W.subgroupOf (prodFst ρ)).map (prodFstHom ρ) := by
    rw [← hBa]
    exact sup_le hB hBa'
  intro y hy
  obtain ⟨w, hw, hwy⟩ := htop (mem_top (prodFstHom ρ ⟨y, hy⟩))
  have hx : ((w⁻¹ * ⟨y, hy⟩ : prodFst ρ) : G) ∈ X := by
    have hk : w⁻¹ * ⟨y, hy⟩ ∈ (prodFstHom ρ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwy, inv_mul_cancel]
    rw [ker_prodFstHom hker, mem_subgroupOf] at hk
    exact hk
  have e : y = (w : G) * ((w⁻¹ * ⟨y, hy⟩ : prodFst ρ) : G) := by
    simp
  rw [e]
  exact mul_mem (mem_subgroupOf.1 hw) (hYW (hXY hx))

theorem isPerfect_prod {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    [Group.IsPerfect B] : Group.IsPerfect (A × B) := by
  rw [Group.isPerfect_def, eq_top_iff]
  rintro ⟨a, b⟩ -
  have h1 : (a, (1 : B)) ∈ commutator (A × B) := by
    have ha : a ∈ commutator A := Group.IsPerfect.mem_commutator
    have := Subgroup.mem_map_of_mem (MonoidHom.inl A B) ha
    rw [_root_.commutator_def, Subgroup.map_commutator] at this
    exact commutator_mono le_top le_top this
  have h2 : ((1 : A), b) ∈ commutator (A × B) := by
    have hb : b ∈ commutator B := Group.IsPerfect.mem_commutator
    have := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
    rw [_root_.commutator_def, Subgroup.map_commutator] at this
    exact commutator_mono le_top le_top this
  simpa using mul_mem h1 h2

theorem le_commutator_sup_of_perfect [Group.IsPerfect S] {X : Subgroup G}
    (hρ : Function.Surjective ρ) (hker : ρ.ker = X.subgroupOf N) : N ≤ ⁅N, N⁆ ⊔ X := by
  haveI : Group.IsPerfect (S × S) := isPerfect_prod
  intro n hn
  have hmap : (⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆).map ρ = ⊤ := by
    rw [map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hρ,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  have hρn : ρ ⟨n, hn⟩ ∈ (⁅(⊤ : Subgroup N), (⊤ : Subgroup N)⁆).map ρ := by
    rw [hmap]
    exact mem_top _
  obtain ⟨c, hc, hcn⟩ := hρn
  have hcG : (c : G) ∈ ⁅N, N⁆ := by
    have := mem_map_of_mem N.subtype hc
    rwa [map_commutator, Subgroup.map_top, range_subtype] at this
  have hx : ((c⁻¹ * ⟨n, hn⟩ : N) : G) ∈ X := by
    have : c⁻¹ * ⟨n, hn⟩ ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcn, inv_mul_cancel]
    rw [hker, mem_subgroupOf] at this
    exact this
  have e : n = (c : G) * ((c⁻¹ * ⟨n, hn⟩ : N) : G) := by
    simp
  rw [e]
  exact mul_mem_sup hcG hx

end Factor

section Swap

variable {G : Type*} [Group G] {S : Type*} [Group S] {N X : Subgroup G} {ρ : N →* S × S} {t : G}

theorem mem_map_conj_prodFst_iff (htN : t ∈ normalizer (N : Set G)) (ht2 : t * t = 1)
    (hswap : ∀ n n' : N, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap) {g : G} :
    g ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom ↔ ∃ h : g ∈ N, (ρ ⟨g, h⟩).1 = 1 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyN, hy2⟩ := (mem_prodFst_iff ρ).1 hy
    have hg : (MulAut.conj t).toMonoidHom y = t * y * t⁻¹ := rfl
    have hgN : t * y * t⁻¹ ∈ N := (mem_normalizer_iff.1 htN y).1 hyN
    rw [hg]
    refine ⟨hgN, ?_⟩
    rw [hswap ⟨y, hyN⟩ ⟨t * y * t⁻¹, hgN⟩ rfl]
    exact hy2
  · rintro ⟨hgN, hg1⟩
    have hyN : t * g * t⁻¹ ∈ N := (mem_normalizer_iff.1 htN g).1 hgN
    have hconj : t * (t * g * t⁻¹) * t⁻¹ = g := by
      rw [hti, show t * (t * g * t) * t = (t * t) * g * (t * t) by group, ht2]
      group
    have hs := hswap ⟨t * g * t⁻¹, hyN⟩ ⟨g, hgN⟩ hconj.symm
    refine ⟨t * g * t⁻¹, (mem_prodFst_iff ρ).2 ⟨hyN, ?_⟩, hconj⟩
    rw [hs] at hg1
    exact hg1

theorem mem_normalizer_ker_of_swap (htN : t ∈ normalizer (N : Set G))
    (hswap : ∀ n n' : N, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap) (hXN : X ≤ N)
    (hker : ρ.ker = X.subgroupOf N) : t ∈ normalizer (X : Set G) := by
  have hker' : ∀ n : N, (n : G) ∈ X ↔ ρ n = 1 := fun n => by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
  have key : ∀ (u u' : G) (hu : u ∈ N) (hu' : u' ∈ N), u' = t * u * t⁻¹ →
      (u ∈ X ↔ u' ∈ X) := by
    intro u u' hu hu' h
    rw [hker' ⟨u, hu⟩, hker' ⟨u', hu'⟩, hswap ⟨u, hu⟩ ⟨u', hu'⟩ h]
    constructor
    · intro h1
      rw [h1]
      rfl
    · intro h1
      simpa using congrArg Prod.swap h1
  rw [mem_normalizer_iff]
  intro x
  by_cases hx : x ∈ N
  · exact key x _ hx ((mem_normalizer_iff.1 htN x).1 hx) rfl
  · have hx' : t * x * t⁻¹ ∉ N := fun h => hx ((mem_normalizer_iff.1 htN x).2 h)
    exact ⟨fun h => (hx (hXN h)).elim, fun h => (hx' (hXN h)).elim⟩

theorem prodFst_sup_map_conj (htN : t ∈ normalizer (N : Set G)) (ht2 : t * t = 1)
    (hswap : ∀ n n' : N, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap)
    (hρ : Function.Surjective ρ) :
    prodFst ρ ⊔ (prodFst ρ).map (MulAut.conj t).toMonoidHom = N := by
  refine le_antisymm (sup_le (prodFst_le ρ) fun g hg =>
    ((mem_map_conj_prodFst_iff htN ht2 hswap).1 hg).1) fun n hn => ?_
  obtain ⟨l, hl⟩ := hρ ((ρ ⟨n, hn⟩).1, 1)
  have hlΛ : (l : G) ∈ prodFst ρ := (mem_prodFst_iff ρ).2 ⟨l.2, congrArg Prod.snd hl⟩
  have hmΛ : ((l⁻¹ * ⟨n, hn⟩ : N) : G) ∈ (prodFst ρ).map (MulAut.conj t).toMonoidHom := by
    refine (mem_map_conj_prodFst_iff htN ht2 hswap).2 ⟨(l⁻¹ * ⟨n, hn⟩ : N).2, ?_⟩
    show (ρ (l⁻¹ * ⟨n, hn⟩)).1 = 1
    rw [map_mul, map_inv, Prod.fst_mul, Prod.fst_inv, hl]
    simp
  have e : n = (l : G) * ((l⁻¹ * ⟨n, hn⟩ : N) : G) := by
    simp
  rw [e]
  exact mul_mem_sup hlΛ hmΛ

theorem commutator_prodFst_map_conj_le (htN : t ∈ normalizer (N : Set G)) (ht2 : t * t = 1)
    (hswap : ∀ n n' : N, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap)
    (hker : ρ.ker = X.subgroupOf N) :
    ⁅prodFst ρ, (prodFst ρ).map (MulAut.conj t).toMonoidHom⁆ ≤ X := by
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨haN, ha2⟩ := (mem_prodFst_iff ρ).1 ha
  obtain ⟨hbN, hb1⟩ := (mem_map_conj_prodFst_iff htN ht2 hswap).1 hb
  have hcN : ⁅a, b⁆ ∈ N := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem haN hbN) (inv_mem haN)) (inv_mem hbN)
  have h1 : ρ ⟨⁅a, b⁆, hcN⟩ = 1 := by
    have e : (⟨⁅a, b⁆, hcN⟩ : N) = ⁅(⟨a, haN⟩ : N), ⟨b, hbN⟩⁆ := rfl
    rw [e, map_commutatorElement]
    refine Prod.ext ?_ ?_
    · simp [commutatorElement_def, hb1]
    · simp [commutatorElement_def, ha2]
  have h2 : (⟨⁅a, b⁆, hcN⟩ : N) ∈ ρ.ker := h1
  rw [hker, mem_subgroupOf] at h2
  exact h2

theorem le_normalizer_map_conj_prodFst (htN : t ∈ normalizer (N : Set G)) :
    N ≤ normalizer (((prodFst ρ).map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
  intro n hn
  have hm : t⁻¹ * n * t ∈ N := by
    have := (mem_normalizer_iff.1 (inv_mem htN) n).1 hn
    rwa [inv_inv] at this
  rw [mem_normalizer_iff]
  intro y
  rw [mem_map_equiv, mem_map_equiv]
  simp only [MulAut.conj_symm_apply]
  rw [show t⁻¹ * (n * y * n⁻¹) * t = (t⁻¹ * n * t) * (t⁻¹ * y * t) * (t⁻¹ * n * t)⁻¹ by group]
  exact mem_normalizer_iff.1 (le_normalizer_prodFst ρ hm) (t⁻¹ * y * t)

theorem inf_prodFst_le_normalizer_map_conj {T : Subgroup G} {r : G}
    (htN : t ∈ normalizer (N : Set G)) (ht2 : t * t = 1)
    (hswap : ∀ n n' : N, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap)
    (hker : ρ.ker = X.subgroupOf N) (hXN : X ≤ N) (hXT : X ≤ T)
    (htX : t ∈ normalizer (X : Set G)) (hrN : r ∈ N) (hrX : r ∈ normalizer (X : Set G)) :
    T ⊓ prodFst ρ ≤ normalizer ((((T ⊓ prodFst ρ).map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj r).toMonoidHom : Subgroup G) : Set G) := by
  set Y : Subgroup G := T ⊓ prodFst ρ
  set Z : Subgroup G := (Y.map (MulAut.conj t).toMonoidHom).map (MulAut.conj r).toMonoidHom
  have hXY : X ≤ Y := le_inf hXT (le_prodFst hXN hker)
  have hXZ : X ≤ Z := by
    calc X = (X.map (MulAut.conj t).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
          rw [map_conj_eq_of_mem_normalizer htX, map_conj_eq_of_mem_normalizer hrX]
      _ ≤ Z := map_mono (map_mono hXY)
  have hZΛt : Z ≤ (prodFst ρ).map (MulAut.conj t).toMonoidHom := by
    calc Z ≤ ((prodFst ρ).map (MulAut.conj t).toMonoidHom).map (MulAut.conj r).toMonoidHom :=
          map_mono (map_mono inf_le_right)
      _ = (prodFst ρ).map (MulAut.conj t).toMonoidHom :=
          map_conj_eq_of_mem_normalizer (le_normalizer_map_conj_prodFst htN hrN)
  have key : ∀ v ∈ Y, ∀ y ∈ Z, v * y * v⁻¹ ∈ Z := by
    intro v hv y hy
    have hc : ⁅v, y⁆ ∈ X := commutator_prodFst_map_conj_le htN ht2 hswap hker
      (commutator_mem_commutator (mem_inf.1 hv).2 (hZΛt hy))
    have e : v * y * v⁻¹ = ⁅v, y⁆ * y := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hXZ hc) hy
  intro v hv
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key v hv y, fun hy => ?_⟩
  have := key v⁻¹ (inv_mem hv) _ hy
  rwa [show v⁻¹ * (v * y * v⁻¹) * v⁻¹⁻¹ = y by group] at this

end Swap

section Centralizer

variable {G : Type*} [Group G]

theorem map_conj_map_conj_comm (H : Subgroup G) {t r : G} (htr : t * r = r * t) :
    (H.map (MulAut.conj r).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (H.map (MulAut.conj t).toMonoidHom).map (MulAut.conj r).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc t * (r * x * r⁻¹) * t⁻¹ = (t * r) * x * (t * r)⁻¹ := by group
    _ = (r * t) * x * (r * t)⁻¹ := by rw [htr]
    _ = r * (t * x * t⁻¹) * r⁻¹ := by group

theorem inf_map_conj_le_centralizer {N Λ S F : Subgroup G} {t r : G}
    (hΛt : Λ ⊔ Λ.map (MulAut.conj t).toMonoidHom = N)
    (hgen : Λ ≤ S ⊔ S.map (MulAut.conj r).toMonoidHom)
    (htS : t ∈ normalizer (S : Set G)) (htr : t * r = r * t)
    (hFS : F ≤ centralizer (S : Set G)) :
    F ⊓ F.map (MulAut.conj r).toMonoidHom ≤ centralizer (N : Set G) := by
  set T : Subgroup G := S ⊔ S.map (MulAut.conj r).toMonoidHom with hT
  have hTt : T.map (MulAut.conj t).toMonoidHom = T := by
    rw [hT, Subgroup.map_sup, map_conj_eq_of_mem_normalizer htS,
      map_conj_map_conj_comm S htr, map_conj_eq_of_mem_normalizer htS]
  have hNT : N ≤ T := by
    rw [← hΛt]
    refine sup_le hgen ?_
    calc Λ.map (MulAut.conj t).toMonoidHom ≤ T.map (MulAut.conj t).toMonoidHom := map_mono hgen
      _ = T := hTt
  have hF : F.map (MulAut.conj r).toMonoidHom ≤
      centralizer ((S.map (MulAut.conj r).toMonoidHom : Subgroup G) : Set G) := by
    rintro _ ⟨f, hf, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have hfs := mem_centralizer_iff.1 (hFS hf) s hs
    show r * s * r⁻¹ * (r * f * r⁻¹) = r * f * r⁻¹ * (r * s * r⁻¹)
    calc r * s * r⁻¹ * (r * f * r⁻¹) = r * (s * f) * r⁻¹ := by group
      _ = r * (f * s) * r⁻¹ := by rw [hfs]
      _ = r * f * r⁻¹ * (r * s * r⁻¹) := by group
  intro x hx
  obtain ⟨hxF, hxFr⟩ := mem_inf.1 hx
  have hxC : x ∈ centralizer (T : Set G) := by
    rw [hT, centralizer_sup_eq]
    exact mem_inf.2 ⟨hFS hxF, hF hxFr⟩
  exact centralizer_le (SetLike.coe_subset_coe.2 hNT) hxC

end Centralizer

section Diagonal

variable {K : Type*} [Field K] [Fintype K] {f : ℕ}

theorem odd_sq_pow_sub_one (hf : 1 ≤ f) : Odd ((2 ^ f) ^ 2 - 1) :=
  Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
    ((Nat.even_pow.2 ⟨even_two, by omega⟩).pow_of_ne_zero two_ne_zero) odd_one

theorem card_le_of_isPGroup_SL2 (hf : 1 ≤ f) (hK : Fintype.card K = 2 ^ f)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hK]
  have hdvd : Nat.card P ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Subgroup.card_subgroup_dvd_card P
  rw [hn, hSL] at hdvd
  have hcop : Nat.Coprime (2 ^ n) ((2 ^ f) ^ 2 - 1) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 (odd_sq_pow_sub_one hf))
  rw [hn]
  exact Nat.le_of_dvd (by positivity) (hcop.dvd_of_dvd_mul_right hdvd)

theorem eq_prod_of_diag_le (hf : 1 ≤ f) (hK : Fintype.card K = 2 ^ f)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hB : Nat.card B = 2 ^ f)
    {V : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)}
    (hV : IsPGroup 2 V) (hcard : Nat.card V = (2 ^ f) ^ 2) (hdiag : ∀ b ∈ B, (b, b) ∈ V) :
    V = B.prod B := by
  have hproj : ∀ φ : Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.SpecialLinearGroup (Fin 2) K, (∀ b, φ (b, b) = b) → V.map φ = B := by
    intro φ hφ
    have hle : B ≤ V.map φ := fun b hb => ⟨(b, b), hdiag b hb, hφ b⟩
    exact (eq_of_le_of_card_ge hle (by
      rw [hB]
      exact card_le_of_isPGroup_SL2 hf hK (hV.map φ))).symm
  have h1 := hproj (MonoidHom.fst _ _) fun b => rfl
  have h2 := hproj (MonoidHom.snd _ _) fun b => rfl
  have hle : V ≤ B.prod B := by
    intro v hv
    rw [mem_prod]
    refine ⟨?_, ?_⟩
    · rw [← h1]
      exact ⟨v, hv, rfl⟩
    · rw [← h2]
      exact ⟨v, hv, rfl⟩
  refine eq_of_le_of_card_ge hle ?_
  rw [hcard, Nat.card_congr (Subgroup.prodEquiv B B).toEquiv, Nat.card_prod, hB, sq]

end Diagonal

section Main

variable {G : Type*} [Group G]

theorem isElementaryAbelian_mono {p : ℕ} {E E' : Subgroup G} (hE : IsElementaryAbelian p E)
    (h : E' ≤ E) : IsElementaryAbelian p E' where
  toIsMulCommutative := ⟨⟨fun a b => by
    have := hE.toIsMulCommutative
    exact Subtype.ext (by
      simpa using congrArg Subtype.val (mul_comm' (⟨a, h a.2⟩ : E) ⟨b, h b.2⟩))⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext (by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hE.exponent_dvd_p ⟨x, h x.2⟩
    simpa using congrArg Subtype.val this)

theorem exists_sylow_inf_prodFst {K : Type*} [Field K] [Fintype K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Fintype.card K = 2 ^ m) {N X S : Subgroup G}
    {ρ : N →* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K}
    (hρ : Function.Surjective ρ) (hker : ρ.ker = X.subgroupOf N) (hXS : X ≤ S)
    (hS2 : IsPGroup 2 S) {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hB : Nat.card B = 2 ^ m) (h : (S.subgroupOf N).map ρ = B.prod B) :
    ∃ P : Sylow 2 (prodFst ρ),
      (P : Subgroup (prodFst ρ)).map (prodFst ρ).subtype = S ⊓ prodFst ρ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup (prodFst ρ) := (S ⊓ prodFst ρ).subgroupOf (prodFst ρ) with hH
  have hH2 : IsPGroup 2 H :=
    (hS2.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hmap : H.map (prodFstHom ρ) = B := by
    ext b
    rw [mem_iff_exists_prodFstHom h]
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, (mem_inf.1 (mem_subgroupOf.1 hs)).1, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, mem_subgroupOf.2 (mem_inf.2 ⟨hs, s.2⟩), rfl⟩
  have hkerH : (prodFstHom ρ).ker ≤ H := by
    rw [ker_prodFstHom hker]
    intro x hx
    exact mem_subgroupOf.2 (mem_inf.2 ⟨hXS (mem_subgroupOf.1 hx), x.2⟩)
  have hindex : H.index = B.index := by
    rw [← hmap]
    exact (H.index_map_eq (surjective_prodFstHom hρ) hkerH).symm
  have hBidx : B.index = (2 ^ m) ^ 2 - 1 := by
    have hcard := B.card_mul_index
    rw [hB, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card,
      hK] at hcard
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hcard
  refine ⟨hH2.toSylow ?_, ?_⟩
  · rw [hindex, hBidx]
    exact (odd_sq_pow_sub_one hm).not_two_dvd_nat
  · show H.map (prodFst ρ).subtype = S ⊓ prodFst ρ
    rw [hH, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]

variable [Finite G]

theorem map_subgroupOf_eq_prod {K : Type*} [Field K] [Fintype K] {m : ℕ} (hm : 1 ≤ m)
    (hK : Fintype.card K = 2 ^ m) {N X S : Subgroup G}
    (ρ : N →* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (hker : ρ.ker = X.subgroupOf N) (hSN : S ≤ N) (hXS : X ≤ S) (hS2 : IsPGroup 2 S)
    (hScard : Nat.card S = (2 ^ m) ^ 2 * Nat.card X)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hB : Nat.card B = 2 ^ m)
    (hdiag : ∀ b ∈ B, ∃ s : N, (s : G) ∈ S ∧ ρ s = (b, b)) :
    (S.subgroupOf N).map ρ = B.prod B := by
  have hXN : X ≤ N := hXS.trans hSN
  have hS2' : IsPGroup 2 (S.subgroupOf N) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hcard : Nat.card ((S.subgroupOf N).map ρ) = (2 ^ m) ^ 2 := by
    have h1 := card_map_mul_card_inf_ker ρ (S.subgroupOf N)
    have h2 : S.subgroupOf N ⊓ ρ.ker = X.subgroupOf N := by
      rw [hker]
      exact inf_of_le_right (fun x hx => mem_subgroupOf.2 (hXS (mem_subgroupOf.1 hx)))
    rw [h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv, hScard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  refine eq_prod_of_diag_le hm hK hB (hS2'.map ρ) hcard fun b hb => ?_
  obtain ⟨s, hs, hρs⟩ := hdiag b hb
  exact ⟨s, mem_subgroupOf.2 hs, hρs⟩

theorem exists_perfect_commuting_factor_of_prodClosure
    {K : Type*} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hm : 2 ≤ m)
    {N X S E F : Subgroup G} {t r : G}
    (ρ : N →* Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)
    (hρ : Function.Surjective ρ) (hker : ρ.ker = X.subgroupOf N) (hXN : X ≤ N)
    (hXsq : ∀ x ∈ X, x * x = 1) (hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x)
    (htN : t ∈ normalizer (N : Set G)) (ht2 : t * t = 1)
    (hswap : ∀ n n' : N, (n' : G) = t * n * t⁻¹ → ρ n' = (ρ n).swap)
    {B : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)} (hB : Nat.card B = 2 ^ m)
    (hSN : S ≤ N) (hXS : X ≤ S) (hS2 : IsPGroup 2 S)
    (hScard : Nat.card S = (2 ^ m) ^ 2 * Nat.card X)
    (hdiag : ∀ b ∈ B, ∃ s : N, (s : G) ∈ S ∧ ρ s = (b, b))
    (htS : t ∈ normalizer (S : Set G))
    (hE : IsElementaryAbelian 2 E) (hEX : X ⊔ E = S)
    (hrN : r ∈ N) {a : Matrix.SpecialLinearGroup (Fin 2) K} (hr : ρ ⟨r, hrN⟩ = (a, a))
    (hBa : B ⊔ B.map (MulAut.conj a).toMonoidHom = ⊤) (htr : t * r = r * t)
    (hFX : F ≤ X) (hFS : F ≤ centralizer (S : Set G)) (htF : t ∈ normalizer (F : Set G))
    (hZF : X ⊓ centralizer (S : Set G) ≤ F)
    (hcX : Nat.card X = (2 ^ m) ^ 6) (hcF : Nat.card F = (2 ^ m) ^ 4)
    (hcW : Nat.card (F ⊓ F.map (MulAut.conj r).toMonoidHom : Subgroup G) = (2 ^ m) ^ 2) :
    ∃ P : Subgroup G, P ≤ prodFst ρ ∧ ⁅P, P⁆ = P ∧ P ⊔ X = prodFst ρ ∧
      ⁅P, P.map (MulAut.conj t).toMonoidHom⁆ = ⊥ ∧
      ∀ Q : Subgroup G, Q ≤ prodFst ρ → ⁅Q, Q⁆ = Q → Q ≤ P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  have hKf : Fintype.card K = 2 ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact hK
  have hm1 : 1 ≤ m := by omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK4
  have hXΛ : X ≤ prodFst ρ := le_prodFst hXN hker
  have hNX : N ≤ normalizer (X : Set G) := le_normalizer_of_ker hXN hker
  have htX : t ∈ normalizer (X : Set G) := mem_normalizer_ker_of_swap htN hswap hXN hker
  have hV : (S.subgroupOf N).map ρ = B.prod B :=
    map_subgroupOf_eq_prod hm1 hKf ρ hker hSN hXS hS2 hScard hB hdiag
  have hΛt := prodFst_sup_map_conj htN ht2 hswap hρ
  have hgen := prodFst_le_sup_map_conj hker hXN hXS hV hrN hr hBa
  have hEle : E ≤ S := le_sup_right.trans hEX.le
  have hE' : IsElementaryAbelian 2 ↥(E ⊓ prodFst ρ) := isElementaryAbelian_mono hE inf_le_left
  have hEX' : X ⊔ E ⊓ prodFst ρ = S ⊓ prodFst ρ := by
    refine le_antisymm (sup_le (le_inf hXS hXΛ) (inf_le_inf_right _ hEle)) ?_
    intro s hs
    obtain ⟨hsS, hsΛ⟩ := mem_inf.1 hs
    have hs' : s ∈ ((E ⊔ X : Subgroup G) : Set G) := by
      rw [sup_comm, hEX]
      exact hsS
    rw [coe_mul_of_left_le_normalizer_right E X (fun e he => hNX (hSN (hEle he)))] at hs'
    obtain ⟨e, he, x, hx, rfl⟩ := Set.mem_mul.1 hs'
    have heΛ : e ∈ prodFst ρ := by
      have := mul_mem hsΛ (inv_mem (hXΛ hx))
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (mem_sup_right (mem_inf.2 ⟨he, heΛ⟩)) (mem_sup_left hx)
  have hZF' : X ⊓ centralizer (N : Set G) ≤ F :=
    (inf_le_inf_left X (centralizer_le (SetLike.coe_subset_coe.2 hSN))).trans hZF
  have hFr : F ⊓ F.map (MulAut.conj r).toMonoidHom ≤ centralizer (N : Set G) :=
    inf_map_conj_le_centralizer hΛt
      (hgen.trans (sup_le_sup inf_le_left (map_mono inf_le_left))) htS htr hFS
  have hZeq : X ⊓ centralizer (N : Set G) = F ⊓ F.map (MulAut.conj r).toMonoidHom := by
    refine le_antisymm (fun x hx => ?_)
      (fun x hx => mem_inf.2 ⟨hFX (mem_inf.1 hx).1, hFr hx⟩)
    obtain ⟨hxX, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨hZF' hx, x, hZF' hx, ?_⟩
    show r * x * r⁻¹ = x
    rw [mem_centralizer_iff.1 hxC r hrN]
    group
  have hZcard : Nat.card (X ⊓ centralizer (N : Set G) : Subgroup G) = (2 ^ m) ^ 2 := by
    rw [hZeq]
    exact hcW
  have hcX' : Nat.card X = (2 ^ m) ^ 4 * Nat.card (X ⊓ centralizer (N : Set G) : Subgroup G) := by
    rw [hZcard, hcX]
    ring
  have hcF' : (2 ^ m) ^ 2 * Nat.card (X ⊓ centralizer (N : Set G) : Subgroup G) ≤ Nat.card F := by
    rw [hZcard, hcF]
    exact (by ring : (2 ^ m) ^ 2 * (2 ^ m) ^ 2 = (2 ^ m) ^ 4).le
  exact exists_perfect_commuting_factor_of_ambient hK hm (E := E ⊓ prodFst ρ) hXΛ (prodFst_le ρ)
    (le_normalizer_prodFst ρ) hNX hXsq hXab htN htX hΛt
    (commutator_prodFst_map_conj_le htN ht2 hswap hker) (le_commutator_sup_of_perfect hρ hker)
    (prodFstHom ρ) (surjective_prodFstHom hρ) (ker_prodFstHom hker) hXS
    (exists_sylow_inf_prodFst hm1 hKf hρ hker hXS hS2 hB hV) (inf_le_inf_right _ hEle) hE' hEX'
    hrN hgen (inf_prodFst_le_normalizer_map_conj htN ht2 hswap hker hXN hXS htX hrN (hNX hrN))
    hFX hFS (map_conj_eq_of_mem_normalizer htF) hZF' hFr hcX' hcF'

end Main

end CFSG.LocalAnalysis.EvenBN.Common
