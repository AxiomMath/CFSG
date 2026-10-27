module

import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GH74.Uniqueness.SU.SU5

open Subgroup

section Basic

variable {G : Type*} [Group G]

theorem isElemAbelian_iff {E : Subgroup G} {p : ℕ} :
    Open.IsElemAbelian p E ↔ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ p = 1 := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨fun a ha b hb => ?_, hp⟩
    have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  · rintro ⟨hc, hp⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, hp⟩

@[expose] def IsE (n : ℕ) (E : Subgroup G) : Prop :=
  Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ n

theorem isElemAbelian_mono {E F : Subgroup G} (h : E ≤ F) (hF : Open.IsElemAbelian 2 F) :
    Open.IsElemAbelian 2 E := CFSG.Open.IsElemAbelian.mono hF h

theorem le_or_le_of_subset_union {E H K : Subgroup G} (h : ∀ e ∈ E, e ∈ H ∨ e ∈ K) :
    E ≤ H ∨ E ≤ K := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  rw [IsConcreteLE.not_le_iff_exists] at h1 h2
  obtain ⟨e, heE, heH⟩ := h1
  obtain ⟨e', heE', heK⟩ := h2
  have heK' : e ∈ K := (h e heE).resolve_left heH
  have heH' : e' ∈ H := (h e' heE').resolve_right heK
  rcases h (e * e') (E.mul_mem heE heE') with h3 | h3
  · exact heH (by simpa using H.mul_mem h3 (H.inv_mem heH'))
  · exact heK (by simpa using K.mul_mem (K.inv_mem heK') h3)

theorem orderOf_eq_four_iff {M : Type*} [Group M] (m : M) :
    orderOf m = 4 ↔ m * m ≠ 1 ∧ (m * m) * (m * m) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : m ^ 4 = (m * m) * (m * m) := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  constructor
  · intro h
    have h4' : m ^ 4 = 1 := by rw [← h]; exact pow_orderOf_eq_one m
    refine ⟨fun h2 => ?_, by rw [← h4]; exact h4'⟩
    have : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [h] at this
    omega
  · rintro ⟨h1, h2⟩
    have key := orderOf_eq_prime_pow (p := 2) (n := 1) (x := m)
      (by rw [pow_one, pow_two]; exact h1) (by norm_num; rw [h4]; exact h2)
    simpa using key

@[expose] def subOfPred (P : G → Prop) (h1 : P 1) (hm : ∀ s t, P s → P t → P (s * t))
    (hi : ∀ s, P s → P s⁻¹) : Subgroup G where
  carrier := {s | P s}
  mul_mem' := fun {a b} ha hb => hm a b ha hb
  one_mem' := h1
  inv_mem' := fun {a} ha => hi a ha

theorem mem_subOfPred {P : G → Prop} {h1 : P 1} {hm : ∀ s t, P s → P t → P (s * t)}
    {hi : ∀ s, P s → P s⁻¹} {s : G} : s ∈ subOfPred P h1 hm hi ↔ P s := Iff.rfl

theorem card_subOfPred [Fintype G] (P : G → Prop) [DecidablePred P] {h1 : P 1}
    {hm : ∀ s t, P s → P t → P (s * t)} {hi : ∀ s, P s → P s⁻¹} :
    Nat.card (subOfPred P h1 hm hi) = (Finset.univ.filter P).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun s => Iff.rfl))

@[expose] def Zc (H : Subgroup G) : Subgroup G := H ⊓ Subgroup.centralizer (H : Set G)

theorem mem_Zc {H : Subgroup G} {u : G} : u ∈ Zc H ↔ u ∈ H ∧ ∀ h ∈ H, u * h = h * u := by
  unfold Zc
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h hh => (h2 h hh).symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun h hh => (h2 h hh).symm⟩

@[expose] def JE (S : Subgroup G) : Subgroup G :=
  ⨆ (E : Subgroup G) (_ : E ≤ S) (_ : Open.IsElemAbelian 2 E)
    (_ : ∀ F : Subgroup G, F ≤ S → Open.IsElemAbelian 2 F → Nat.card F ≤ Nat.card E), E

theorem JE_eq_sup {S A B : Subgroup G} (hA : A ≤ S) (hB : B ≤ S) (hAE : IsE 4 A) (hBE : IsE 4 B)
    (hmax : ∀ F : Subgroup G, F ≤ S → Open.IsElemAbelian 2 F → Nat.card F ≤ 2 ^ 4)
    (huniq : ∀ E : Subgroup G, E ≤ S → IsE 4 E → E = A ∨ E = B) : JE S = A ⊔ B := by
  apply le_antisymm
  · refine iSup_le fun E => iSup_le fun hES => iSup_le fun hEE => iSup_le fun hEm => ?_
    have h1 : Nat.card E = 2 ^ 4 := by
      apply le_antisymm (hmax E hES hEE)
      calc 2 ^ 4 = Nat.card A := hAE.2.symm
        _ ≤ Nat.card E := hEm A hA hAE.1
    rcases huniq E hES ⟨hEE, h1⟩ with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  · have hAm : ∀ F : Subgroup G, F ≤ S → Open.IsElemAbelian 2 F → Nat.card F ≤ Nat.card A :=
      fun F hF hFE => by rw [hAE.2]; exact hmax F hF hFE
    have hBm : ∀ F : Subgroup G, F ≤ S → Open.IsElemAbelian 2 F → Nat.card F ≤ Nat.card B :=
      fun F hF hFE => by rw [hBE.2]; exact hmax F hF hFE
    refine sup_le ?_ ?_
    · exact le_iSup_of_le A (le_iSup_of_le hA (le_iSup_of_le hAE.1 (le_iSup_of_le hAm le_rfl)))
    · exact le_iSup_of_le B (le_iSup_of_le hB (le_iSup_of_le hBE.1 (le_iSup_of_le hBm le_rfl)))

theorem pRank_eq_of [Finite G] {H : Subgroup G} {n : ℕ} (hex : ∃ E : Subgroup G, E ≤ H ∧ IsE n E)
    (hle : ∀ E : Subgroup G, E ≤ H → Open.IsElemAbelian 2 E → Nat.card E ≤ 2 ^ n) :
    Open.pRank 2 H = n := by
  unfold Open.pRank
  apply IsGreatest.csSup_eq
  constructor
  · obtain ⟨E, hE, hE1, hE2⟩ := hex
    exact ⟨E, hE, hE1, hE2⟩
  · rintro k ⟨E, hE, hE1, hE2⟩
    have := hle E hE hE1
    rw [hE2] at this
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem card_le_card_of_finset_subset [Finite G] {N : Subgroup G} {s : Finset G}
    (h : ∀ x ∈ s, x ∈ N) : s.card ≤ Nat.card N := by
  calc s.card = (s : Set G).ncard := (Set.ncard_coe_finset s).symm
    _ ≤ (N : Set G).ncard := Set.ncard_le_ncard (fun x hx => h x hx) (Set.toFinite _)
    _ = Nat.card N := (Nat.card_coe_set_eq (N : Set G)).symm

theorem card_le_card_of_subset_finset {N : Subgroup G} {s : Finset G} (h : ∀ x ∈ N, x ∈ s) :
    Nat.card N ≤ s.card := by
  calc Nat.card N = (N : Set G).ncard := Nat.card_coe_set_eq (N : Set G)
    _ ≤ (s : Set G).ncard := Set.ncard_le_ncard (fun x hx => h x hx) (Set.toFinite _)
    _ = s.card := Set.ncard_coe_finset s

theorem normal_le_of_class_four [Fintype G] [DecidableEq G] (N U : Subgroup G) (hN : N.Normal)
    (hcard : Nat.card N ≤ 4)
    (hcl : ∀ n ∈ N, n ≠ 1 → n ∉ U → 4 ≤ (Finset.univ.image (fun g : G => g * n * g⁻¹)).card) :
    N ≤ U := by
  intro n hn
  by_contra hnU
  have hn1 : n ≠ 1 := by
    rintro rfl; exact hnU U.one_mem
  have h4 := hcl n hn hn1 hnU
  have hsub : ∀ x ∈ insert 1 (Finset.univ.image (fun g : G => g * n * g⁻¹)), x ∈ N := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨g, _, rfl⟩
    · exact N.one_mem
    · exact hN.conj_mem n hn g
  have h1 : (1 : G) ∉ Finset.univ.image (fun g : G => g * n * g⁻¹) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro g hg
    apply hn1
    calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
      _ = 1 := by rw [hg]; group
  have hc := card_le_card_of_finset_subset hsub
  rw [Finset.card_insert_of_notMem h1] at hc
  omega

theorem card_sup_mul_card_inf_of_commute [Finite G] (L R : Subgroup G)
    (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup G) * Nat.card (L ⊓ R : Subgroup G) = Nat.card L * Nat.card R := by
  let μ : L × R →* G := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : G) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : G), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : G)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]; exact this

end Basic

section Map

variable {M G : Type*} [Group M] [Group G]

theorem isElemAbelian_map_iff {f : M →* G} (hf : Function.Injective f) {X : Subgroup M} :
    Open.IsElemAbelian 2 (X.map f) ↔ Open.IsElemAbelian 2 X := by
  rw [isElemAbelian_iff, isElemAbelian_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · have hab := h1 (f a) (Subgroup.mem_map_of_mem f ha) (f b) (Subgroup.mem_map_of_mem f hb)
      exact hf (by rw [map_mul, map_mul]; exact hab)
    · have ha2 := h2 (f a) (Subgroup.mem_map_of_mem f ha)
      exact hf (by rw [map_pow, map_one]; exact ha2)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
      rw [← map_mul, ← map_mul, h1 a' ha' b' hb']
    · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
      rw [← map_pow, h2 a' ha', map_one]

theorem isE_map {f : M →* G} (hf : Function.Injective f) {X : Subgroup M} {n : ℕ} :
    IsE n (X.map f) ↔ IsE n X := by
  unfold IsE
  rw [isElemAbelian_map_iff hf, Subgroup.card_map_of_injective hf]

theorem isE_comap {f : M →* G} (hf : Function.Injective f) {E : Subgroup G} (hE : E ≤ f.range)
    {n : ℕ} (h : IsE n E) : IsE n (E.comap f) := by
  rw [← isE_map hf, Subgroup.map_comap_eq_self hE]; exact h

theorem Zc_map {f : M →* G} (hf : Function.Injective f) (X : Subgroup M) :
    Zc (X.map f) = (Zc X).map f := by
  ext u
  rw [mem_Zc]
  constructor
  · rintro ⟨hu, hc⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hu
    refine Subgroup.mem_map.2 ⟨m, mem_Zc.2 ⟨hm, fun h hh => hf ?_⟩, rfl⟩
    rw [map_mul, map_mul]; exact hc (f h) (Subgroup.mem_map_of_mem f hh)
  · rintro hu
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hu
    rw [mem_Zc] at hm
    refine ⟨Subgroup.mem_map_of_mem f hm.1, fun h hh => ?_⟩
    obtain ⟨h', hh', rfl⟩ := Subgroup.mem_map.1 hh
    rw [← map_mul, ← map_mul, hm.2 h' hh']

theorem card_range_of_injective {f : M →* G} (hf : Function.Injective f) :
    Nat.card f.range = Nat.card M :=
  (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem exists_eq_map_of_le_range {f : M →* G} {E : Subgroup G} (hE : E ≤ f.range) :
    ∃ X : Subgroup M, X.map f = E := ⟨E.comap f, Subgroup.map_comap_eq_self hE⟩

end Map

end CFSG.GH74.Uniqueness.SU.SU5
