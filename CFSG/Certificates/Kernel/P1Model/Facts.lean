module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecG
public import CFSG.LocalAnalysis.ComponentClassification.Sol76LayerFix
public import CFSG.Certificates.Kernel.PermCent.OrbGroup
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1AutModel
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecA
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1CheckSpecB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Facts

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.SmallOddCore

variable {n : ℕ}

@[expose] def A6Normal (A₀ : Subgroup (Equiv.Perm (Fin n))) (v : Equiv.Perm (Fin n)) : Prop :=
  ∃ K : Subgroup (Equiv.Perm (Fin n)), K ≤ A₀ ⊓ centralizer ({v} : Set (Equiv.Perm (Fin n))) ∧
    A₀ ⊓ centralizer ({v} : Set (Equiv.Perm (Fin n))) ≤ normalizer (K : Set (Equiv.Perm (Fin n))) ∧
    Nonempty (↥K ≃* alternatingGroup (Fin 6))

inductive RepFacts (A₀ Aut : Subgroup (Equiv.Perm (Fin n))) (t : Equiv.Perm (Fin n)) : Prop
  | small (K : Subgroup (Equiv.Perm (Fin n)))
      (hle : K ≤ A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))))
      (hnorm : A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ≤
        normalizer (K : Set (Equiv.Perm (Fin n))))
      (hcard : Nat.card K ∣ 288)
      (hpow : ∃ a, K.relIndex (A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) = 2 ^ a)
      (hfive : ¬ 5 ∣ Nat.card ↥(A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))))) :
      RepFacts A₀ Aut t
  | noA6 (hout : t ∉ A₀)
      (hno : ∀ L : Subgroup (Equiv.Perm (Fin n)),
        L ≤ A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) → Nat.card L = 360 →
        A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ≤
          normalizer (L : Set (Equiv.Perm (Fin n))) → False) :
      RepFacts A₀ Aut t
  | a6 (L : Subgroup (Equiv.Perm (Fin n)))
      (hle : L ≤ A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))))
      (hnorm : A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ≤
        normalizer (L : Set (Equiv.Perm (Fin n))))
      (hcard : Nat.card L = 360)
      (hpow : ∃ a, L.relIndex (A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) = 2 ^ a)
      (hodd : L ≤ Q81.oddPart (A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))))
      (hiso : Nonempty (↥L ≃* alternatingGroup (Fin 6)))
      (hconfig : ∀ v ∈ Aut, orderOf v = 2 → v * t = t * v →
        (∃ l ∈ L, orderOf l = 2 ∧ orderOf (v * l) = 8) → A6Normal A₀ v) :
      RepFacts A₀ Aut t

theorem orderOf_conj_inv {G : Type*} [Group G] (g x : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have e : g⁻¹ * x * g = MulAut.conj g⁻¹ x := by simp
  rw [e, MulEquiv.orderOf_eq]

theorem inf_centralizer_conj_of_mem_normalizer {G : Type*} [Group G] (H : Subgroup G) {d : G}
    (hd : d ∈ normalizer (H : Set G)) (v : G) :
    H ⊓ centralizer ({d * v * d⁻¹} : Set G) =
      (H ⊓ centralizer ({v} : Set G)).map (MulAut.conj d).toMonoidHom := by
  ext x
  simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨hx, hxv⟩
    refine ⟨d⁻¹ * x * d, ⟨?_, ?_⟩, by group⟩
    · have h1 := (mem_normalizer_iff.mp (inv_mem hd) x).mp hx
      rwa [inv_inv] at h1
    · calc d⁻¹ * x * d * v = d⁻¹ * (x * (d * v * d⁻¹)) * d := by group
        _ = d⁻¹ * ((d * v * d⁻¹) * x) * d := by rw [hxv]
        _ = v * (d⁻¹ * x * d) := by group
  · rintro ⟨y, ⟨hy, hyv⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.mp hd y).mp hy, ?_⟩
    calc d * y * d⁻¹ * (d * v * d⁻¹) = d * (y * v) * d⁻¹ := by group
      _ = d * (v * y) * d⁻¹ := by rw [hyv]
      _ = d * v * d⁻¹ * (d * y * d⁻¹) := by group

theorem a6Normal_conj {A₀ : Subgroup (Equiv.Perm (Fin n))} {d v : Equiv.Perm (Fin n)}
    (hd : d ∈ normalizer (A₀ : Set (Equiv.Perm (Fin n)))) (h : A6Normal A₀ v) :
    A6Normal A₀ (d * v * d⁻¹) := by
  obtain ⟨K, hKC, hKN, ⟨e⟩⟩ := h
  rw [A6Normal, inf_centralizer_conj_of_mem_normalizer A₀ hd v]
  exact ⟨K.map (MulAut.conj d).toMonoidHom, map_mono hKC, map_conj_le_normalizer hKN d,
    ⟨(K.equivMapOfInjective _ (MulAut.conj d).injective).symm.trans e⟩⟩

theorem a6Normal_of_le {A₀ L : Subgroup (Equiv.Perm (Fin n))} {t : Equiv.Perm (Fin n)}
    (hle : L ≤ A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))))
    (hnorm : A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ≤
      normalizer (L : Set (Equiv.Perm (Fin n))))
    (hiso : Nonempty (↥L ≃* alternatingGroup (Fin 6))) : A6Normal A₀ t :=
  ⟨L, hle, hnorm, hiso⟩

theorem oddPart_eq_of_le {G : Type} [Group G] {C L : Subgroup G} (hle : L ≤ C)
    (hnorm : C ≤ normalizer (L : Set G)) (hpow : ∃ a, L.relIndex C = 2 ^ a)
    (hodd : L ≤ Q81.oddPart C) : Q81.oddPart C = L := by
  obtain ⟨a, ha⟩ := hpow
  exact le_antisymm (oddPart_le_of_relIndex hle hnorm ha) hodd

theorem no360_of_not_dvd {G : Type} [Group G] {C : Subgroup G} (h5 : ¬ 5 ∣ Nat.card C)
    (L : Subgroup G) (hLC : L ≤ C) (hL : Nat.card L = 360) : False :=
  h5 ((by norm_num : 5 ∣ 360).trans (hL ▸ card_dvd_of_le hLC))

theorem no360_of_five {G : Type} [Group G] [Finite G] {C : Subgroup G} {gs : Set G}
    (hgs : ∀ g ∈ gs, g ∈ C ∧ g ^ 5 = 1) (hord : 360 < Nat.card (closure gs))
    (hidx : ¬ 360 ∣ Nat.card C ∨ ¬ 5 ∣ Nat.card C / 360) (L : Subgroup G) (hLC : L ≤ C)
    (hL : Nat.card L = 360) (hN : C ≤ normalizer (L : Set G)) : False := by
  have h360 : 360 ∣ Nat.card C := hL ▸ card_dvd_of_le hLC
  have hidx5 : ¬ 5 ∣ Nat.card C / 360 := by
    rcases hidx with h1 | h1
    · exact absurd h360 h1
    · exact h1
  have hrel : L.relIndex C = Nat.card C / 360 := by
    have h1 := relIndex_mul_card_of_le hLC
    rw [hL] at h1
    rw [← h1, Nat.mul_div_cancel _ (by norm_num)]
  have hKL : closure gs ≤ L := by
    rw [closure_le]
    intro g hg
    obtain ⟨hgC, hg5⟩ := hgs g hg
    refine mem_of_coprime_relIndex hLC hN hgC ?_
    rw [hrel]
    rcases (Nat.dvd_prime Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one hg5) with h1 | h1
    · rw [h1]
      exact Nat.coprime_one_left _
    · rw [h1]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hidx5
  have := card_le_of_le hKL
  omega

noncomputable def mulEquivOfSurjCard {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hc : Nat.card A = Nat.card B) : A ≃* B :=
  MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hc.le)

theorem nonempty_equiv_alternating_six_of_card {x₁ x₂ : Equiv.Perm (Fin n)}
    {y₁ y₂ : Equiv.Perm (Fin 6)} (hy₁ : Odd (orderOf y₁)) (hy₂ : Odd (orderOf y₂))
    (hY : Nat.card (closure ({y₁, y₂} : Set (Equiv.Perm (Fin 6)))) = 360)
    (hX : Nat.card (closure ({x₁, x₂} : Set (Equiv.Perm (Fin n)))) = 360)
    (hD : Nat.card (closure ({pairHom n (x₁, y₁), pairHom n (x₂, y₂)} :
      Set (Equiv.Perm (Fin (n + 6))))) = 360) :
    Nonempty (↥(closure ({x₁, x₂} : Set (Equiv.Perm (Fin n)))) ≃* alternatingGroup (Fin 6)) := by
  set D : Subgroup (Equiv.Perm (Fin n) × Equiv.Perm (Fin 6)) := closure {(x₁, y₁), (x₂, y₂)}
  have hDmap : D.map (pairHom n) =
      closure ({pairHom n (x₁, y₁), pairHom n (x₂, y₂)} : Set (Equiv.Perm (Fin (n + 6)))) := by
    rw [MonoidHom.map_closure, Set.image_pair]
  have hDcard : Nat.card D = 360 := by
    rw [← card_map_of_injective pairHom_injective, hDmap, hD]
  have h1 : D.map (MonoidHom.fst _ _) = closure ({x₁, x₂} : Set (Equiv.Perm (Fin n))) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have h2 : D.map (MonoidHom.snd _ _) = closure ({y₁, y₂} : Set (Equiv.Perm (Fin 6))) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have e₁ : ↥D ≃* ↥(closure ({x₁, x₂} : Set (Equiv.Perm (Fin n)))) :=
    (mulEquivOfSurjCard _ ((MonoidHom.fst _ _).subgroupMap_surjective D)
      (by rw [hDcard, h1, hX])).trans (MulEquiv.subgroupCongr h1)
  have e₂ : ↥D ≃* ↥(closure ({y₁, y₂} : Set (Equiv.Perm (Fin 6)))) :=
    (mulEquivOfSurjCard _ ((MonoidHom.snd _ _).subgroupMap_surjective D)
      (by rw [hDcard, h2, hY])).trans (MulEquiv.subgroupCongr h2)
  have hA6 : closure ({y₁, y₂} : Set (Equiv.Perm (Fin 6))) = alternatingGroup (Fin 6) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [closure_le]
      rintro _ (rfl | rfl)
      · exact mem_alternatingGroup_of_odd hy₁
      · exact mem_alternatingGroup_of_odd hy₂
    · rw [hY, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
  exact ⟨e₁.symm.trans (e₂.trans (MulEquiv.subgroupCongr hA6))⟩

theorem isPGroup_zpowers_of_orderOf {G : Type*} [Group G] {x : G} (hx : orderOf x = 2) :
    IsPGroup 2 (zpowers x) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])

theorem exists_conj_mem_of_le {G : Type*} [Group G] [Finite G] {H S : Subgroup G} (hSH : S ≤ H)
    (hS : Nat.card S = 2 ^ (Nat.card H).factorization 2) {x : G} (hxH : x ∈ H)
    (hx : orderOf x = 2) : ∃ d ∈ H, d⁻¹ * x * d ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : Nat.card (S.subgroupOf H) = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hS]
    exact Nat.card_congr (subgroupOfEquivOfLe hSH).toEquiv
  have hx' : orderOf (⟨x, hxH⟩ : H) = 2 := by rw [Subgroup.orderOf_mk, hx]
  obtain ⟨d, hd⟩ := CFSG.KC.OrbGroup.exists_conj_mem_of_card (S.subgroupOf H) hS'
    (isPGroup_zpowers_of_orderOf hx')
  refine ⟨d, d.2, ?_⟩
  rw [mem_subgroupOf] at hd
  simpa using hd

theorem cover_of_sylow {A₀ : Subgroup (Equiv.Perm (Fin n))} {U : Equiv.Perm (Fin n)}
    (hU : U ∈ normalizer (A₀ : Set (Equiv.Perm (Fin n)))) {reps : Set (Equiv.Perm (Fin n))}
    {S : Subgroup (Equiv.Perm (Fin n))} (hSH : S ≤ A₀ ⊔ zpowers U)
    (hS : Nat.card S = 2 ^ (Nat.card ↥(A₀ ⊔ zpowers U)).factorization 2)
    (htest : ∀ s ∈ S, orderOf s = 2 → ∃ t ∈ reps, ∃ g ∈ A₀, s = g * t * g⁻¹)
    (hUcl : ∀ t ∈ reps, ∃ t' ∈ reps, ∃ g ∈ A₀, U * t * U⁻¹ = g * t' * g⁻¹) :
    ∀ τ ∈ A₀ ⊔ zpowers U, orderOf τ = 2 → ∃ t ∈ reps, ∃ g ∈ A₀, τ = g * t * g⁻¹ := by
  set Cl : Set (Equiv.Perm (Fin n)) := {x | ∃ t ∈ reps, ∃ g ∈ A₀, x = g * t * g⁻¹}
  have hgen : ∀ d ∈ (A₀ : Set (Equiv.Perm (Fin n))) ∪ {U}, ∀ x ∈ Cl, d * x * d⁻¹ ∈ Cl := by
    rintro d (hd | hd) x ⟨t, ht, g, hg, rfl⟩
    · exact ⟨t, ht, d * g, A₀.mul_mem hd hg, by group⟩
    · rw [Set.mem_singleton_iff] at hd
      subst hd
      obtain ⟨t', ht', g', hg', e⟩ := hUcl t ht
      have hUg : d * g * d⁻¹ ∈ A₀ := (mem_normalizer_iff.mp hU g).mp hg
      refine ⟨t', ht', d * g * d⁻¹ * g', A₀.mul_mem hUg hg', ?_⟩
      calc d * (g * t * g⁻¹) * d⁻¹ = d * g * d⁻¹ * (d * t * d⁻¹) * (d * g * d⁻¹)⁻¹ := by group
        _ = _ := by rw [e]; group
  have hall : ∀ d ∈ A₀ ⊔ zpowers U, ∀ x ∈ Cl, d * x * d⁻¹ ∈ Cl := by
    intro d hd
    have hcl : A₀ ⊔ zpowers U = closure ((A₀ : Set (Equiv.Perm (Fin n))) ∪ {U}) := by
      rw [Subgroup.closure_union, closure_eq, zpowers_eq_closure]
    rw [hcl] at hd
    induction hd using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one =>
      intro y hy
      rw [one_mul, inv_one, mul_one]
      exact hy
    | mul a b _ _ ha hb =>
      intro y hy
      have e : a * b * y * (a * b)⁻¹ = a * (b * y * b⁻¹) * a⁻¹ := by group
      rw [e]
      exact ha _ (hb y hy)
    | inv a _ ha =>
      intro y hy
      obtain ⟨z, hz, e⟩ := CFSG.KC.OrbGroup.surj_of_mapsTo (fun z => a * z * a⁻¹)
        (fun u v e => by simpa using e) ha y hy
      have e2 : a⁻¹ * y * a⁻¹⁻¹ = z := by
        rw [← e]
        group
      rw [e2]
      exact hz
  intro τ hτ hτ2
  obtain ⟨d, hd, hdS⟩ := exists_conj_mem_of_le hSH hS hτ hτ2
  have h1 := hall d hd _ (htest _ hdS (by rw [orderOf_conj_inv, hτ2]))
  have e : d * (d⁻¹ * τ * d) * d⁻¹ = τ := by group
  rwa [e] at h1

theorem config_of_sylow {A₀ L : Subgroup (Equiv.Perm (Fin n))} {t w : Equiv.Perm (Fin n)}
    (hLeq : Q81.oddPart (A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) = L)
    (hwA : w ∈ normalizer (A₀ : Set (Equiv.Perm (Fin n)))) (hwt : w * t = t * w)
    {T : Subgroup (Equiv.Perm (Fin n))}
    (hTD : T ≤ A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ⊔ zpowers w)
    (hTcard : Nat.card T = 2 ^ (Nat.card ↥(A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ⊔
      zpowers w)).factorization 2)
    (htest : ∀ v ∈ T, orderOf v = 2 → (v ∈ A₀ ↔ w ∈ A₀) →
      (∃ l ∈ L, orderOf l = 2 ∧ orderOf (v * l) = 8) → A6Normal A₀ v)
    {v : Equiv.Perm (Fin n)} (hv2 : orderOf v = 2) (hvt : v * t = t * v) (hvw : v * w⁻¹ ∈ A₀)
    (hl : ∃ l ∈ L, orderOf l = 2 ∧ orderOf (v * l) = 8) : A6Normal A₀ v := by
  set C := A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) with hCdef
  set D := C ⊔ zpowers w with hDdef
  have hwc : w ∈ centralizer ({t} : Set (Equiv.Perm (Fin n))) :=
    mem_centralizer_singleton_iff.mpr hwt
  have hDN : D ≤ normalizer (A₀ : Set (Equiv.Perm (Fin n))) :=
    sup_le (inf_le_left.trans le_normalizer) ((zpowers_le).mpr hwA)
  have hDc : D ≤ centralizer ({t} : Set (Equiv.Perm (Fin n))) :=
    sup_le inf_le_right ((zpowers_le).mpr hwc)
  have hCd : ∀ d ∈ D, C.map (MulAut.conj d).toMonoidHom = C := by
    intro d hd
    have hdt : d * t * d⁻¹ = t := by
      have := mem_centralizer_singleton_iff.mp (hDc hd)
      rw [this]
      group
    rw [hCdef, ← inf_centralizer_conj_of_mem_normalizer A₀ (hDN hd) t, hdt]
  have hLd : ∀ d ∈ D, L.map (MulAut.conj d).toMonoidHom = L := by
    intro d hd
    rw [← hLeq, map_oddPart_of_injective _ (MulAut.conj d).injective, hCd d hd]
  have hvD : v ∈ D := by
    have hvwC : v * w⁻¹ ∈ C := by
      refine mem_inf.mpr ⟨hvw, ?_⟩
      exact mul_mem (mem_centralizer_singleton_iff.mpr hvt) (inv_mem hwc)
    have : v = v * w⁻¹ * w := by group
    rw [this]
    exact mul_mem (mem_sup_left hvwC) (mem_sup_right (mem_zpowers w))
  obtain ⟨d, hd, hdT⟩ := exists_conj_mem_of_le hTD hTcard hvD hv2
  have hdA := hDN hd
  have hvA : v ∈ A₀ ↔ w ∈ A₀ := by
    constructor
    · intro h
      have : w = (v * w⁻¹)⁻¹ * v := by group
      rw [this]
      exact mul_mem (inv_mem hvw) h
    · intro h
      have : v = v * w⁻¹ * w := by group
      rw [this]
      exact mul_mem hvw h
  have hv'A : d⁻¹ * v * d ∈ A₀ ↔ w ∈ A₀ := by
    rw [← hvA]
    have h1 := mem_normalizer_iff.mp (inv_mem hdA) v
    rw [inv_inv] at h1
    exact h1.symm
  obtain ⟨l, hlL, hl2, hl8⟩ := hl
  have hl'L : d⁻¹ * l * d ∈ L := by
    rw [← hLd d⁻¹ (inv_mem hd)]
    exact ⟨l, hlL, by simp⟩
  have h8' : orderOf (d⁻¹ * v * d * (d⁻¹ * l * d)) = 8 := by
    have e : d⁻¹ * v * d * (d⁻¹ * l * d) = d⁻¹ * (v * l) * d := by group
    rw [e, orderOf_conj_inv, hl8]
  have h' := htest _ hdT (by rw [orderOf_conj_inv, hv2]) hv'A
    ⟨_, hl'L, by rw [orderOf_conj_inv, hl2], h8'⟩
  have h1 := a6Normal_conj hdA h'
  have e : d * (d⁻¹ * v * d) * d⁻¹ = v := by group
  rwa [e] at h1

theorem p1ModelFacts_of_facts {P : Type} [Group P] (M : AutModel P n)
    {A₀ : Subgroup (Equiv.Perm (Fin n))} (hrange : M.π.range = A₀)
    {reps : Set (Equiv.Perm (Fin n))}
    (hcover : ∀ τ ∈ M.T.range, orderOf τ = 2 → ∃ t ∈ reps, ∃ g ∈ A₀, τ = g * t * g⁻¹)
    (hrep : ∀ t ∈ reps, RepFacts A₀ M.T.range t) : P1ModelFacts P := by
  classical
  have hA₀T : A₀ ≤ M.T.range := by
    rw [← hrange]
    rintro _ ⟨x, rfl⟩
    exact ⟨MulAut.conj x, M.T_conj x⟩
  refine ⟨fun s hs => ?_, ?_⟩
  ·
    set σ := M.π s
    have hσA : σ ∈ A₀ := hrange ▸ ⟨s, rfl⟩
    have hσ2 : orderOf σ = 2 := by rw [orderOf_injective M.π M.inj s, hs]
    obtain ⟨t, ht, g, hg, hσg⟩ := hcover σ (hA₀T hσA) hσ2
    have hσg' : M.π s = g * t * g⁻¹ := hσg
    have hcard : Nat.card ↥(Q81.oddPart (centralizer ({s} : Set P))) =
        Nat.card ↥(Q81.oddPart (A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))))) := by
      rw [← card_map_of_injective M.inj, map_oddPart_of_injective _ M.inj,
        map_centralizer_eq M.π M.inj hrange, hσg', card_oddPart_conj A₀ hg]
    rw [hcard]
    have hin : t ∈ A₀ := by
      have h1 : t = g⁻¹ * σ * g := by rw [hσg]; group
      rw [h1]
      exact A₀.mul_mem (A₀.mul_mem (A₀.inv_mem hg) hσA) hg
    rcases hrep t ht with ⟨K, hle, hnorm, hK, ⟨a, ha⟩, -⟩ | ⟨hout, -⟩ |
        ⟨L, hle, hnorm, hL, hpow, hodd, -, -⟩
    · exact Or.inl ((card_dvd_of_le (oddPart_le_of_relIndex hle hnorm ha)).trans hK)
    · exact absurd hin hout
    · exact Or.inr (by rw [oddPart_eq_of_le hle hnorm hpow hodd, hL])
  ·
    intro α β L ℓ hα hβ hαβ hL hLα hLn hℓ hℓ2 h8
    set τ := M.T α with hτdef
    set v := M.T β with hvdef
    have hτ2 : orderOf τ = 2 := (M.orderOf_T α).trans hα
    have hv2 : orderOf v = 2 := (M.orderOf_T β).trans hβ
    have hτv : τ * v = v * τ := by rw [hτdef, hvdef, ← map_mul, hαβ, map_mul]
    set L' := L.map M.π with hL'def
    have hL'card : Nat.card L' = 360 := by rw [card_map_of_injective M.inj, hL]
    have hL'C : L' ≤ A₀ ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin n))) := by
      rintro _ ⟨y, hy, rfl⟩
      refine mem_inf.mpr ⟨hrange ▸ ⟨y, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff]
      exact ((M.fixed_iff α y).mp (hLα y hy)).symm
    have hL'N : A₀ ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin n))) ≤
        normalizer (L' : Set (Equiv.Perm (Fin n))) := by
      refine Sol76.le_normalizer_of_forall_conj_mem ?_
      rintro c hc _ ⟨y, hy, rfl⟩
      obtain ⟨hcA, hcτ⟩ := mem_inf.mp hc
      rw [← hrange] at hcA
      obtain ⟨c₀, rfl⟩ := hcA
      rw [mem_centralizer_singleton_iff] at hcτ
      have hc₀ : α c₀ = c₀ := (M.fixed_iff α c₀).mpr hcτ.symm
      exact ⟨c₀ * y * c₀⁻¹, hLn c₀ hc₀ y hy, by rw [map_mul, map_mul, map_inv]⟩
    set lam := M.π ℓ
    have hlamL' : lam ∈ L' := ⟨ℓ, hℓ, rfl⟩
    have hlam2 : orderOf lam = 2 := by rw [orderOf_injective M.π M.inj, hℓ2]
    have hvlam : orderOf (v * lam) = 8 := by
      have e : v * lam = M.T (β * MulAut.conj ℓ) := by rw [map_mul, M.T_conj]
      rw [e, M.orderOf_T, h8]
    obtain ⟨t, ht, g, hg, hτg⟩ := hcover τ ⟨α, rfl⟩ hτ2
    set L₀ := L'.map (MulAut.conj g⁻¹).toMonoidHom with hL₀def
    have hCconj : A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) =
        (A₀ ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin n)))).map
          (MulAut.conj g⁻¹).toMonoidHom := by
      have h1 : t = g⁻¹ * τ * g⁻¹⁻¹ := by rw [hτg]; group
      rw [h1, inf_centralizer_conj A₀ (A₀.inv_mem hg) τ]
    have hL₀C : L₀ ≤ A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) := by
      rw [hCconj]
      exact map_mono hL'C
    have hL₀card : Nat.card L₀ = 360 := by
      rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hL'card]
    have hL₀N : A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ≤
        normalizer (L₀ : Set (Equiv.Perm (Fin n))) := by
      rw [hCconj]
      exact map_conj_le_normalizer hL'N g⁻¹
    obtain ⟨Lt, hle, hnorm, hLt, ⟨a, ha⟩, hodd, hconfig⟩ : ∃ Lt : Subgroup (Equiv.Perm (Fin n)),
        Lt ≤ A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ∧
        A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) ≤
          normalizer (Lt : Set (Equiv.Perm (Fin n))) ∧ Nat.card Lt = 360 ∧
        (∃ a, Lt.relIndex (A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) = 2 ^ a) ∧
        Lt ≤ Q81.oddPart (A₀ ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n)))) ∧
        (∀ v ∈ M.T.range, orderOf v = 2 → v * t = t * v →
          (∃ l ∈ Lt, orderOf l = 2 ∧ orderOf (v * l) = 8) → A6Normal A₀ v) := by
      rcases hrep t ht with ⟨K, -, -, -, -, h5⟩ | ⟨-, hno⟩ |
          ⟨Lt, hle, hnorm, hLt, hpow, hodd, -, hconf⟩
      · exact (no360_of_not_dvd h5 L₀ hL₀C hL₀card).elim
      · exact (hno L₀ hL₀C hL₀card hL₀N).elim
      · exact ⟨Lt, hle, hnorm, hLt, hpow, hodd, hconf⟩
    have hL₀eq : Lt = L₀ := by
      apply Subgroup.eq_of_le_of_card_ge
      · refine hodd.trans (oddPart_le_of_relIndex hL₀C hL₀N (a := a) ?_)
        have h1 := relIndex_mul_card_of_le hL₀C
        have h2 := relIndex_mul_card_of_le hle
        rw [hL₀card] at h1
        rw [hLt] at h2
        rw [← ha]
        exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 360) (h1.trans h2.symm)
      · rw [hL₀card, hLt]
    set v₀ := g⁻¹ * v * g with hv₀def
    set lam₀ := g⁻¹ * lam * g with hlam₀def
    have hv₀T : v₀ ∈ M.T.range :=
      mul_mem (mul_mem (inv_mem (hA₀T hg)) ⟨β, rfl⟩) (hA₀T hg)
    have hv₀t : v₀ * t = t * v₀ := by
      have ht' : t = g⁻¹ * τ * g := by rw [hτg]; group
      rw [ht']
      calc g⁻¹ * v * g * (g⁻¹ * τ * g) = g⁻¹ * (v * τ) * g := by group
        _ = g⁻¹ * (τ * v) * g := by rw [hτv]
        _ = g⁻¹ * τ * g * (g⁻¹ * v * g) := by group
    have hlam₀ : lam₀ ∈ Lt := by
      rw [hL₀eq]
      exact ⟨lam, hlamL', by simp [hlam₀def]⟩
    have h8₀ : orderOf (v₀ * lam₀) = 8 := by
      have e : v₀ * lam₀ = g⁻¹ * (v * lam) * g := by
        rw [hv₀def, hlam₀def]
        group
      rw [e, orderOf_conj_inv, hvlam]
    have hgood := hconfig v₀ hv₀T (by rw [hv₀def, orderOf_conj_inv, hv2]) hv₀t
      ⟨lam₀, hlam₀, by rw [hlam₀def, orderOf_conj_inv, hlam2], h8₀⟩
    have hgoodv : A6Normal A₀ v := by
      have h1 := a6Normal_conj (le_normalizer hg) hgood
      have e : g * v₀ * g⁻¹ = v := by
        rw [hv₀def]
        group
      rwa [e] at h1
    obtain ⟨M', hM'C, hM'N, ⟨eA⟩⟩ := hgoodv
    have hM'A : M' ≤ M.π.range := hrange ▸ (hM'C.trans inf_le_left)
    refine ⟨M'.comap M.π, ?_, ?_, ?_⟩
    · intro y hy
      have hyc := (mem_inf.mp (hM'C hy)).2
      rw [mem_centralizer_singleton_iff] at hyc
      exact (M.fixed_iff β y).mpr hyc.symm
    · intro c' hc' y hy
      have hc'C : M.π c' ∈ A₀ ⊓ centralizer ({v} : Set (Equiv.Perm (Fin n))) := by
        refine mem_inf.mpr ⟨hrange ▸ ⟨c', rfl⟩, ?_⟩
        rw [mem_centralizer_singleton_iff]
        exact ((M.fixed_iff β c').mp hc').symm
      have h1 := (mem_normalizer_iff.mp (hM'N hc'C) (M.π y)).mp hy
      change M.π (c' * y * c'⁻¹) ∈ M'
      rw [map_mul, map_mul, map_inv]
      exact h1
    · have e1 : ↥(M'.comap M.π) ≃* ↥M' :=
        ((M'.comap M.π).equivMapOfInjective M.π M.inj).trans
          (MulEquiv.subgroupCongr (map_comap_eq_self hM'A))
      exact ⟨e1.trans eA⟩

end CFSG.ComponentClassification.HarrisLit.P1
