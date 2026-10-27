module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.Quasithin.Background.FFC12E

public section

namespace CFSG.Quasithin.B69K

open CFSG.Quasithin.B69

variable {V : Type} [CommGroup V] [Finite V]

theorem perm_eq_one_of_central {m : ℕ} (hm : 5 ≤ m) {a : Equiv.Perm (Fin m)}
    (ha : a ∈ alternatingGroup (Fin m)) (hc : ∀ τ ∈ alternatingGroup (Fin m), τ * a = a * τ) :
    a = 1 := by
  have hcard : 4 ≤ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hz : (⟨a, ha⟩ : alternatingGroup (Fin m)) ∈ Subgroup.center (alternatingGroup (Fin m)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hc g g.2)
  rw [alternatingGroup.center_eq_bot hcard, Subgroup.mem_bot] at hz
  exact congrArg Subtype.val hz

theorem alt_stab_not_normal {m : ℕ} (hm : 5 ≤ m) (p : Fin m)
    (h : ∀ τ ∈ alternatingGroup (Fin m), ∀ s ∈ alternatingGroup (Fin m), s p = p →
      (τ * s * τ⁻¹) p = p) : False := by
  have hc : 2 < (Finset.univ.erase p).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨q, hq, r, hr, s, hs, hqr, hqs, hrs⟩ := Finset.two_lt_card.1 hc
  rw [Finset.mem_erase] at hq hr hs
  have hq' : q ≠ p := hq.1
  have hr' : r ≠ p := hr.1
  have hs' : s ≠ p := hs.1
  have hcard : 5 ≤ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact hm
  have hstab : ∀ σ : Equiv.Perm (Fin m),
      σ ∈ MulAction.stabilizer (Equiv.Perm (Fin m)) p ↔ σ p = p := fun σ => by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  set N : Subgroup (alternatingGroup (Fin m)) :=
    (MulAction.stabilizer (Equiv.Perm (Fin m)) p).subgroupOf (alternatingGroup (Fin m)) with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => Subgroup.mem_subgroupOf.2 ?_⟩
    have hn' : (n : Equiv.Perm (Fin m)) p = p := (hstab _).1 (Subgroup.mem_subgroupOf.1 hn)
    rw [hstab, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact h _ g.2 _ n.2 hn'
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top hcard (N := N) with hbot | htop
  · have hg1A : Equiv.swap q r * Equiv.swap q s ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hqr,
        Equiv.Perm.sign_swap hqs]
      rfl
    have hg1p : (Equiv.swap q r * Equiv.swap q s) p = p := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hq'.symm hs'.symm,
        Equiv.swap_apply_of_ne_of_ne hq'.symm hr'.symm]
    have hg1q : (Equiv.swap q r * Equiv.swap q s) q = s := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hqs.symm hrs.symm]
    have hmem : (⟨Equiv.swap q r * Equiv.swap q s, hg1A⟩ : alternatingGroup (Fin m)) ∈ N :=
      Subgroup.mem_subgroupOf.2 ((hstab _).2 hg1p)
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : Equiv.swap q r * Equiv.swap q s = 1 := congrArg Subtype.val hmem
    have h2 : (Equiv.swap q r * Equiv.swap q s) q = q := by
      rw [h1, Equiv.Perm.one_apply]
    rw [hg1q] at h2
    exact hqs h2.symm
  · have hg2A : Equiv.swap p q * Equiv.swap p r ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap hq'.symm,
        Equiv.Perm.sign_swap hr'.symm]
      rfl
    have hg2p : (Equiv.swap p q * Equiv.swap p r) p = r := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne hr' hqr.symm]
    have hmem : (⟨Equiv.swap p q * Equiv.swap p r, hg2A⟩ : alternatingGroup (Fin m)) ∈ N := by
      rw [htop]
      exact Subgroup.mem_top _
    have hp2 : (Equiv.swap p q * Equiv.swap p r) p = p :=
      (hstab _).1 (Subgroup.mem_subgroupOf.1 hmem)
    rw [hg2p] at hp2
    exact hr' hp2

theorem exists_perm_conj_of_normalizes {m : ℕ} (hm5 : 5 ≤ m) (hm6 : m ≠ 6)
    (φ : Equiv.Perm (Fin m) →* MulAut V) (hφi : Function.Injective φ) (L : Subgroup (MulAut V))
    (hφL : L = (alternatingGroup (Fin m)).map φ) {t : MulAut V}
    (htn : t ∈ Subgroup.normalizer (L : Set (MulAut V))) :
    ∃ σ : Equiv.Perm (Fin m), ∀ a ∈ alternatingGroup (Fin m),
      φ (σ * a * σ⁻¹) = t * φ a * t⁻¹ := by
  subst hφL
  let f : alternatingGroup (Fin m) →* ↥((alternatingGroup (Fin m)).map φ) :=
    { toFun := fun a => ⟨φ (a : Equiv.Perm (Fin m)), Subgroup.mem_map_of_mem φ a.2⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ (a : Equiv.Perm (Fin m)) (b : Equiv.Perm (Fin m))) }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply hφi
      exact congrArg Subtype.val hab
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
      exact ⟨⟨a, ha⟩, rfl⟩
  let e : alternatingGroup (Fin m) ≃* ↥((alternatingGroup (Fin m)).map φ) :=
    MulEquiv.ofBijective f hf
  let cL : MulAut ↥((alternatingGroup (Fin m)).map φ) :=
    ((alternatingGroup (Fin m)).map φ).normalizerMonoidHom ⟨t, htn⟩
  have hcL : ∀ x : ↥((alternatingGroup (Fin m)).map φ),
      ((cL x : ↥((alternatingGroup (Fin m)).map φ)) : MulAut V) = t * (x : MulAut V) * t⁻¹ :=
    fun _ => rfl
  let ψ : alternatingGroup (Fin m) ≃* alternatingGroup (Fin m) :=
    MulEquiv.trans e (MulEquiv.trans cL e.symm)
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m hm5
    hm6).2 ψ
  have hψ : ∀ x : alternatingGroup (Fin m),
      φ ((ψ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
        t * φ (x : Equiv.Perm (Fin m)) * t⁻¹ := by
    intro x
    have h2 : e (ψ x) = cL (e x) := e.apply_symm_apply _
    calc φ ((ψ x : alternatingGroup (Fin m)) : Equiv.Perm (Fin m))
        = ((e (ψ x) : ↥((alternatingGroup (Fin m)).map φ)) : MulAut V) := rfl
      _ = ((cL (e x) : ↥((alternatingGroup (Fin m)).map φ)) : MulAut V) := by rw [h2]
      _ = t * ((e x : ↥((alternatingGroup (Fin m)).map φ)) : MulAut V) * t⁻¹ := hcL (e x)
      _ = t * φ (x : Equiv.Perm (Fin m)) * t⁻¹ := rfl
  refine ⟨σ, fun a ha => ?_⟩
  have h1 : ((ψ ⟨a, ha⟩ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = σ * a * σ⁻¹ := by
    rw [← hσ]
    exact MulAut.conjNormal_apply σ ⟨a, ha⟩
  rw [← h1]
  exact hψ ⟨a, ha⟩

theorem stab_le_M {X T M L : Subgroup (MulAut V)} (hmp : MinParabolic X T M)
    (hO2 : CFSG.Open.pCoreOf 2 X = ⊥) (hL : CFSG.Open.IsComponentOf L X) {m : ℕ} (hm5 : 5 ≤ m)
    (hm6 : m ≠ 6) (φ : Equiv.Perm (Fin m) →* MulAut V) (hφi : Function.Injective φ)
    (hφL : L = (alternatingGroup (Fin m)).map φ) {p : Fin m}
    (hp : ∀ g ∈ (T ⊓ L).comap φ, g p = p)
    (hpu : ∀ q : Fin m, (∀ g ∈ (T ⊓ L).comap φ, g q = q) → q = p) :
    ∀ a ∈ alternatingGroup (Fin m), a p = p → φ a ∈ M := by
  have hLX : L ≤ X := hL.1
  have hTX : T ≤ X := hmp.isSylow.1
  have hA_L : ∀ a ∈ alternatingGroup (Fin m), φ a ∈ L := by
    intro a ha
    rw [hφL]
    exact Subgroup.mem_map_of_mem φ ha
  have hL_A : ∀ x ∈ L, ∃ a ∈ alternatingGroup (Fin m), φ a = x := by
    intro x hx
    rw [hφL] at hx
    exact Subgroup.mem_map.1 hx
  have hconjA : ∀ g σ' : Equiv.Perm (Fin m),
      σ' * g * σ'⁻¹ ∈ alternatingGroup (Fin m) ↔ g ∈ alternatingGroup (Fin m) := by
    intro g σ'
    constructor
    · intro hg
      have h1 := (inferInstance : (alternatingGroup (Fin m)).Normal).conj_mem _ hg σ'⁻¹
      have e : σ'⁻¹ * (σ' * g * σ'⁻¹) * σ'⁻¹⁻¹ = g := by group
      rwa [e] at h1
    · intro hg
      exact (inferInstance : (alternatingGroup (Fin m)).Normal).conj_mem _ hg σ'
  have hstab : ∀ σ : Equiv.Perm (Fin m),
      σ ∈ MulAction.stabilizer (Equiv.Perm (Fin m)) p ↔ σ p = p := fun σ => by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  set S : Subgroup (Equiv.Perm (Fin m)) :=
    alternatingGroup (Fin m) ⊓ MulAction.stabilizer (Equiv.Perm (Fin m)) p with hS
  have hSmem : ∀ σ, σ ∈ S ↔ σ ∈ alternatingGroup (Fin m) ∧ σ p = p := fun σ => by
    rw [hS, Subgroup.mem_inf, hstab]
  set Y₀ : Subgroup (MulAut V) := S.map φ with hY₀
  have hY₀L : Y₀ ≤ L := by
    intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.1 hy
    exact hA_L σ ((hSmem σ).1 hσ).1
  have hY₀X : Y₀ ≤ X := hY₀L.trans hLX
  have hY₀mem : ∀ a ∈ alternatingGroup (Fin m), a p = p → φ a ∈ Y₀ := fun a ha hap =>
    Subgroup.mem_map_of_mem φ ((hSmem a).2 ⟨ha, hap⟩)
  set C : Subgroup (MulAut V) := Subgroup.centralizer (L : Set (MulAut V)) with hC_def
  have hC : ∀ c ∈ C, ∀ l ∈ L, l * c = c * l := fun c hc l hl =>
    Subgroup.mem_centralizer_iff.1 hc l hl
  set V₀ : Subgroup (Equiv.Perm (Fin m)) := (T ⊓ L).comap φ with hV₀
  let Q : Subgroup (MulAut V) :=
    { carrier := {x | ∃ y ∈ Y₀, ∃ c ∈ C, x = y * c}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, c₁, hc₁, rfl⟩ ⟨y₂, hy₂, c₂, hc₂, rfl⟩
        refine ⟨y₁ * y₂, Y₀.mul_mem hy₁ hy₂, c₁ * c₂, C.mul_mem hc₁ hc₂, ?_⟩
        have hcomm : c₁ * y₂ = y₂ * c₁ := (hC c₁ hc₁ y₂ (hY₀L hy₂)).symm
        calc y₁ * c₁ * (y₂ * c₂) = y₁ * (c₁ * y₂) * c₂ := by group
          _ = y₁ * (y₂ * c₁) * c₂ := by rw [hcomm]
          _ = y₁ * y₂ * (c₁ * c₂) := by group
      one_mem' := ⟨1, Y₀.one_mem, 1, C.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨y, hy, c, hc, rfl⟩
        refine ⟨y⁻¹, Y₀.inv_mem hy, c⁻¹, C.inv_mem hc, ?_⟩
        rw [mul_inv_rev]
        exact (hC c⁻¹ (C.inv_mem hc) y⁻¹ (L.inv_mem (hY₀L hy))).symm }
  have hYQ : ∀ y ∈ Y₀, y ∈ Q := fun y hy => ⟨y, hy, 1, C.one_mem, by simp⟩
  have hCQ : ∀ c ∈ C, c ∈ Q := fun c hc => ⟨1, Y₀.one_mem, c, hc, by simp⟩
  have hQL : ∀ x ∈ Q, x ∈ L → x ∈ Y₀ := by
    rintro x ⟨y, hy, c, hc, rfl⟩ hx
    have hcL : c ∈ L := by
      have h1 : y⁻¹ * (y * c) ∈ L := L.mul_mem (L.inv_mem (hY₀L hy)) hx
      simpa using h1
    have hc1 : c = 1 := by
      obtain ⟨a, ha, rfl⟩ := hL_A c hcL
      have hcomm : ∀ τ ∈ alternatingGroup (Fin m), τ * a = a * τ := by
        intro τ hτ
        have h2 := hC (φ a) hc (φ τ) (hA_L τ hτ)
        rw [← map_mul, ← map_mul] at h2
        exact hφi h2
      rw [perm_eq_one_of_central hm5 ha hcomm, map_one]
    rw [hc1, mul_one]
    exact hy
  have hcaseA : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set (MulAut V)) →
      ∀ y ∈ Y₀, t * y * t⁻¹ ∈ Y₀ := by
    intro t ht hn y hy
    have hn' := Subgroup.mem_normalizer_iff.1 hn
    obtain ⟨a, haS, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨ha, hap⟩ := (hSmem a).1 haS
    obtain ⟨σ, hσ⟩ := exists_perm_conj_of_normalizes hm5 hm6 φ hφi L hφL hn
    have hiff : ∀ h : Equiv.Perm (Fin m), h ∈ V₀ ↔ σ * h * σ⁻¹ ∈ V₀ := by
      intro h
      by_cases hhA : h ∈ alternatingGroup (Fin m)
      · rw [hV₀, Subgroup.mem_comap, Subgroup.mem_comap, hσ h hhA]
        constructor
        · intro hh
          obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hh
          exact Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem ht h1) (T.inv_mem ht),
            (hn' (φ h)).1 h2⟩
        · intro hh
          obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hh
          refine Subgroup.mem_inf.2 ⟨?_, (hn' (φ h)).2 h2⟩
          have e : t⁻¹ * (t * φ h * t⁻¹) * t = φ h := by group
          rw [← e]
          exact T.mul_mem (T.mul_mem (T.inv_mem ht) h1) ht
      · have h1 : h ∉ V₀ := fun hh => by
          obtain ⟨b, hb, hbeq⟩ := hL_A (φ h)
            (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hh)).2
          rw [← hφi hbeq] at hhA
          exact hhA hb
        have h2 : σ * h * σ⁻¹ ∉ V₀ := fun hh => by
          obtain ⟨b, hb, hbeq⟩ := hL_A (φ (σ * h * σ⁻¹))
            (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hh)).2
          have hcA : σ * h * σ⁻¹ ∈ alternatingGroup (Fin m) := by
            rw [← hφi hbeq]
            exact hb
          exact hhA ((hconjA h σ).1 hcA)
        exact iff_of_false h1 h2
    have hσp : σ p = p := by
      refine hpu (σ p) (fun g hg => ?_)
      have hgσ : σ⁻¹ * g * σ ∈ V₀ := by
        rw [hiff]
        have e : σ * (σ⁻¹ * g * σ) * σ⁻¹ = g := by group
        rw [e]
        exact hg
      have key := hp _ hgσ
      simp only [Equiv.Perm.mul_apply] at key
      exact Equiv.Perm.inv_eq_iff_eq.1 key
    have hσinv : σ⁻¹ p = p := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact hσp.symm
    have hcA : σ * a * σ⁻¹ ∈ alternatingGroup (Fin m) := (hconjA a σ).2 ha
    have hfix : (σ * a * σ⁻¹) p = p := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσinv, hap, hσp]
    rw [← hσ a ha]
    exact Subgroup.mem_map_of_mem φ ((hSmem _).2 ⟨hcA, hfix⟩)
  have hcaseB : ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set (MulAut V)) →
      ∀ y ∈ L, t * y * t⁻¹ ∈ C := by
    intro t ht hn y hy
    have htX : t ∈ X := hTX ht
    have hL' : CFSG.Open.IsComponentOf (B6.conjSub t L) X := B113.isComponentOf_conj hL htX
    have hne : L ≠ B6.conjSub t L := by
      intro heq
      apply hn
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hx' := SetLike.ext_iff.1 heq (t * x * t⁻¹)
      rw [B6.mem_conjSub] at hx'
      have e : t⁻¹ * (t * x * t⁻¹) * t = x := by group
      rw [e] at hx'
      exact hx'.symm
    have hmemL' : t * y * t⁻¹ ∈ B6.conjSub t L := by
      rw [B6.mem_conjSub]
      have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      rw [e]
      exact hy
    rw [hC_def, Subgroup.mem_centralizer_iff]
    intro h hh
    exact (components_mul_comm_of_ne hL hL' hne _ hmemL' h hh).symm
  set gens : Set (MulAut V) := {x | ∃ t ∈ T, ∃ y ∈ Y₀, x = t * y * t⁻¹} with hgens
  set J : Subgroup (MulAut V) := Subgroup.closure gens with hJ
  have hgenQ : ∀ x ∈ gens, x ∈ Q := by
    rintro x ⟨t, ht, y, hy, rfl⟩
    by_cases hn : t ∈ Subgroup.normalizer (L : Set (MulAut V))
    · exact hYQ _ (hcaseA t ht hn y hy)
    · exact hCQ _ (hcaseB t ht hn y (hY₀L hy))
  have hJQ : J ≤ Q := (Subgroup.closure_le Q).2 hgenQ
  have hgenX : ∀ x ∈ gens, x ∈ X := by
    rintro x ⟨t, ht, y, hy, rfl⟩
    exact X.mul_mem (X.mul_mem (hTX ht) (hY₀X hy)) (X.inv_mem (hTX ht))
  have hJX : J ≤ X := (Subgroup.closure_le X).2 hgenX
  have hY₀J : Y₀ ≤ J := fun y hy =>
    Subgroup.subset_closure (show y ∈ gens from ⟨1, T.one_mem, y, hy, by simp⟩)
  have hTn : T ≤ Subgroup.normalizer (J : Set (MulAut V)) := by
    intro t ht
    apply CFSG.Quasithin.B69.mem_normalizer_closure_of_gens
    · rintro x ⟨s, hs, y, hy, rfl⟩
      exact Subgroup.subset_closure
        (show t * (s * y * s⁻¹) * t⁻¹ ∈ gens from ⟨t * s, T.mul_mem ht hs, y, hy, by group⟩)
    · rintro x ⟨s, hs, y, hy, rfl⟩
      exact Subgroup.subset_closure
        (show t⁻¹ * (s * y * s⁻¹) * t ∈ gens from
          ⟨t⁻¹ * s, T.mul_mem (T.inv_mem ht) hs, y, hy, by group⟩)
  have hXn : ¬ X ≤ Subgroup.normalizer (J : Set (MulAut V)) := by
    intro hn
    apply alt_stab_not_normal hm5 p
    intro τ hτ s hs hsp
    have hsY : φ s ∈ Y₀ := hY₀mem s hs hsp
    have hτL : φ τ ∈ L := hA_L τ hτ
    have hJ' : φ τ * φ s * (φ τ)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.1 (hn (hLX hτL)) (φ s)).1 (hY₀J hsY)
    have hLm : φ τ * φ s * (φ τ)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hτL (hY₀L hsY)) (L.inv_mem hτL)
    obtain ⟨s', hs', heq⟩ := Subgroup.mem_map.1 (hQL _ (hJQ hJ') hLm)
    have heq' : φ s' = φ (τ * s * τ⁻¹) := by
      rw [heq, map_mul, map_mul, map_inv]
    have hs'eq : s' = τ * s * τ⁻¹ := hφi heq'
    rw [← hs'eq]
    exact ((hSmem s').1 hs').2
  have hRX : X ⊓ Subgroup.normalizer (J : Set (MulAut V)) < X :=
    lt_of_le_of_ne inf_le_left (fun h => hXn (by rw [← h]; exact inf_le_right))
  have hTR : T ≤ X ⊓ Subgroup.normalizer (J : Set (MulAut V)) := le_inf hTX hTn
  have hRM : X ⊓ Subgroup.normalizer (J : Set (MulAut V)) ≤ M := hmp.le_of_lt hTR hRX
  have hJM : J ≤ M := fun x hx => hRM ⟨hJX hx, Subgroup.le_normalizer hx⟩
  intro a ha hap
  exact hJM (hY₀J (hY₀mem a ha hap))

end CFSG.Quasithin.B69K

end
