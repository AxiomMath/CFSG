module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolTrans
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolOrbit
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolFaith
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Perfect

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin CFSG.RankThree.PartTwo Equiv Equiv.Perm MulAction
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender

@[expose] def ExitSixteenTransitive : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin 16)), Function.Injective ψ →
      alternatingGroup (Fin 16) ≤ ψ.range →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender H A →
      IsPretransitive ((A.subgroupOf H).map ψ) (Fin 16) →
      ∀ a : ↥H, (a : MulAut V) ∈ A → (a : MulAut V) ≠ 1 →
      ∀ B : Subgroup (MulAut V), B ≤ A → (a : MulAut V) ∉ B →
        (∀ g ∈ A, g ∈ B ∨ (a : MulAut V) * g ∈ B) →
      ∀ ι : Fin 8 ↪ Fin 16,
        (∀ b : ↥H, (b : MulAut V) ∈ B → ψ b ∈ permSetStab (Set.range ι)) →
        (∀ i j : Fin 8, ∃ b : ↥H, (b : MulAut V) ∈ B ∧ ψ b (ι i) = ι j) →
        (∀ x, ψ a x ∈ Set.range ι ↔ x ∉ Set.range ι) →
      ∀ (hMW : transM ψ ι (ψ a) ≤ stabSub (fixV (Subgroup.zpowers (a : MulAut V))))
        (hC : ∀ k : ↥(transM ψ ι (ψ a)),
          (∀ w ∈ fixV (Subgroup.zpowers (a : MulAut V)), (k : MulAut V) w = w) →
            restrictHom ψ ι _ (transM_le ψ ι (ψ a)) k = 1),
        (NatVia (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)
            (commV (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))) ∨
          Exotic (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)) →
        False

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)} {A : Subgroup (MulAut V)}

theorem false_of_exitSixteenTransitive (hexit : ExitSixteenTransitive) (hn : n = 16)
    (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hA : IsFFStarOffender H A)
    (htr : IsPretransitive ((A.subgroupOf H).map ψ) (Fin n)) (a : ↥H) (haA : (a : MulAut V) ∈ A)
    (ha1 : (a : MulAut V) ≠ 1) (B : Subgroup (MulAut V)) (hBA : B ≤ A) (haB : (a : MulAut V) ∉ B)
    (hAB : ∀ g ∈ A, g ∈ B ∨ (a : MulAut V) * g ∈ B) (ι : Fin (n / 2) ↪ Fin n)
    (hBΓ : ∀ b : ↥H, (b : MulAut V) ∈ B → ψ b ∈ permSetStab (Set.range ι))
    (hBtr : ∀ i j : Fin (n / 2), ∃ b : ↥H, (b : MulAut V) ∈ B ∧ ψ b (ι i) = ι j)
    (ht : ∀ x, ψ a x ∈ Set.range ι ↔ x ∉ Set.range ι)
    (hMW : transM ψ ι (ψ a) ≤ stabSub (fixV (Subgroup.zpowers (a : MulAut V))))
    (hC : ∀ k : ↥(transM ψ ι (ψ a)),
      (∀ w ∈ fixV (Subgroup.zpowers (a : MulAut V)), (k : MulAut V) w = w) →
        restrictHom ψ ι _ (transM_le ψ ι (ψ a)) k = 1)
    (hout : NatVia (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)
        (commV (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))) ∨
      Exotic (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)) : False := by
  subst hn
  exact hexit V hV H ψ hψ hAlt A hA htr a haA ha1 B hBA haB hAB ι hBΓ hBtr ht hMW hC hout

theorem step_transitive (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hA : IsFFStarOffender H A) (hn : 9 ≤ n)
    (hT : ∀ m, 8 ≤ m → m < n → TPerm m) (htr : IsPretransitive ((A.subgroupOf H).map ψ) (Fin n))
    (hexit : ExitSixteenTransitive) : False := by
  classical
  have : Finite (MulAut V) := Finite.of_injective _ DFunLike.coe_injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsExp2 ((A.subgroupOf H).map ψ) := isExp2_map_subgroupOf hA.2.2.1
  have hcomm := hA.2.2.1.1
  have hsq := hA.2.2.1.2
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hcardAb : Nat.card ((A.subgroupOf H).map ψ) = n := by
    have := card_eq_of_isExp2_of_pretransitive hE (Ω := Fin n)
    rwa [Nat.card_fin] at this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hE.isPGroup :
    ∃ k, Nat.card ((A.subgroupOf H).map ψ) = 2 ^ k)
  have hk4 : 4 ≤ k := by
    by_contra h
    push Not at h
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at this
    omega
  have hn2 : n / 2 + n / 2 = n := by
    have : n = 2 * 2 ^ (k - 1) := by
      rw [← hcardAb, hk, ← pow_succ']
      congr 1
      omega
    omega
  have hn16 : 16 ≤ n := by
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    omega
  set ω₀ : Fin n := ⟨0, by omega⟩ with hω₀
  have hreg : ∀ g : ↥H, (g : MulAut V) ∈ A → ψ g ω₀ = ω₀ → g = 1 := by
    intro g hg hgω
    have h1 : (⟨ψ g, ⟨g, hg, rfl⟩⟩ : ↥((A.subgroupOf H).map ψ)) ∈ stabilizer _ ω₀ := hgω
    rw [stabilizer_eq_bot_of_isExp2 hE ω₀, Subgroup.mem_bot] at h1
    exact hψ ((congrArg Subtype.val h1).trans (map_one ψ).symm)
  have htrans : ∀ x, ∃ g : ↥H, (g : MulAut V) ∈ A ∧ ψ g ω₀ = x := fun x => by
    obtain ⟨⟨g, hg⟩, hgx⟩ := htr.exists_smul_eq ω₀ x
    obtain ⟨g', hg', rfl⟩ := mem_map_subgroupOf.1 hg
    exact ⟨g', hg', hgx⟩
  obtain ⟨a, haA, ha1⟩ : ∃ a : ↥H, (a : MulAut V) ∈ A ∧ (a : MulAut V) ≠ 1 := by
    obtain ⟨g, hg, hgω⟩ := htrans ⟨1, by omega⟩
    refine ⟨g, hg, fun h => ?_⟩
    have h1 : g = 1 := Subtype.ext h
    rw [h1, map_one] at hgω
    exact absurd (congrArg Fin.val hgω) (by simp [hω₀])
  have ha2 : (a : MulAut V) ^ 2 = 1 := hsq _ haA
  have hψa2 : ∀ x, ψ a (ψ a x) = x := fun x => by
    have h1 : a * a = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, ha2]; rfl)
    have h2 := congrArg (fun g : Perm (Fin n) => g x) (congrArg ψ h1)
    simpa only [map_mul, map_one, Perm.mul_apply, Perm.one_apply] using h2
  obtain ⟨B, hBA, haB, hAB⟩ := exists_hyperplane hcomm hsq haA ha1
  have hmemB : ∀ {y}, y ∈ orbit ((B.subgroupOf H).map ψ) ω₀ ↔
      ∃ b : ↥H, (b : MulAut V) ∈ B ∧ ψ b ω₀ = y := fun {y} => by
    rw [mem_orbit_iff_perm]
    constructor
    · rintro ⟨_, hg, rfl⟩
      obtain ⟨b, hb, rfl⟩ := mem_map_subgroupOf.1 hg
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨ψ b, ⟨b, hb, rfl⟩, rfl⟩
  have hΓ : ∀ x, x ∈ orbit ((B.subgroupOf H).map ψ) ω₀ ↔
      ψ a x ∉ orbit ((B.subgroupOf H).map ψ) ω₀ := by
    intro x
    constructor
    · rintro hx hax
      obtain ⟨b, hb, rfl⟩ := hmemB.1 hx
      obtain ⟨b', hb', hb'x⟩ := hmemB.1 hax
      have h1 : ψ (b'⁻¹ * a * b) ω₀ = ω₀ := by
        rw [map_mul, map_mul, map_inv, Perm.mul_apply, Perm.mul_apply, ← hb'x,
          perm_inv_apply_apply]
      have h2 := hreg _ (A.mul_mem (A.mul_mem (A.inv_mem (hBA hb')) haA) (hBA hb)) h1
      apply haB
      have h3 : (a : MulAut V) = (b' : MulAut V) * (b : MulAut V)⁻¹ := by
        have := congrArg (fun g : ↥H => (b' : MulAut V) * (g : MulAut V) * (b : MulAut V)⁻¹) h2
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one] at this
        calc (a : MulAut V)
            = (b' : MulAut V) * ((b' : MulAut V)⁻¹ * a * b) * (b : MulAut V)⁻¹ := by group
          _ = (b' : MulAut V) * 1 * (b : MulAut V)⁻¹ := this
          _ = _ := by rw [mul_one]
      rw [h3]
      exact B.mul_mem hb' (B.inv_mem hb)
    · intro hax
      obtain ⟨g, hg, rfl⟩ := htrans x
      rcases hAB _ hg with hgB | hagB
      · exact hmemB.2 ⟨g, hgB, rfl⟩
      · exfalso
        apply hax
        refine hmemB.2 ⟨a * g, hagB, ?_⟩
        rw [map_mul, Perm.mul_apply]
  have hfinΓ := Set.toFinite (orbit ((B.subgroupOf H).map ψ) ω₀)
  have hTcard : hfinΓ.toFinset.card = n / 2 := by
    have hcompl : hfinΓ.toFinsetᶜ = hfinΓ.toFinset.map (ψ a).toEmbedding := by
      ext x
      simp only [Finset.mem_compl, Set.Finite.mem_toFinset, Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · intro hx
        refine ⟨ψ a x, (hΓ (ψ a x)).2 ?_, hψa2 x⟩
        rw [hψa2]
        exact hx
      · rintro ⟨y, hy, rfl⟩
        exact (hΓ y).1 hy
    have h1 := Finset.card_add_card_compl hfinΓ.toFinset
    rw [hcompl, Finset.card_map, Fintype.card_fin] at h1
    omega
  obtain ⟨ι, hι⟩ := exists_embedding_range_eq hfinΓ.toFinset hTcard
  have hιΓ : ∀ x, x ∈ Set.range ι ↔ x ∈ orbit ((B.subgroupOf H).map ψ) ω₀ := fun x =>
    (hι x).trans (Set.Finite.mem_toFinset _)
  have ht : ∀ x, ψ a x ∈ Set.range ι ↔ x ∉ Set.range ι := fun x => by
    rw [hιΓ, hιΓ, hΓ (ψ a x), hψa2]
  have hBtr : ∀ i j : Fin (n / 2), ∃ b : ↥H, (b : MulAut V) ∈ B ∧ ψ b (ι i) = ι j := by
    intro i j
    obtain ⟨b₁, hb₁, h₁⟩ := hmemB.1 ((hιΓ (ι i)).1 ⟨i, rfl⟩)
    obtain ⟨b₂, hb₂, h₂⟩ := hmemB.1 ((hιΓ (ι j)).1 ⟨j, rfl⟩)
    refine ⟨b₂ * b₁⁻¹, B.mul_mem hb₂ (B.inv_mem hb₁), ?_⟩
    rw [map_mul, map_inv, Perm.mul_apply, ← h₁, perm_inv_apply_apply, h₂]
  have hκsurj := fun σ => restrictHom_transM_surjective (ψ := ψ) (ι := ι) (t := ψ a) hAlt ht hψa2 σ
  have hκinj := restrictHom_transM_injective (ψ := ψ) (ι := ι) (t := ψ a) hψ ht hψa2
  have hκA : alternatingGroup (Fin (n / 2)) ≤
      (restrictHom ψ ι _ (transM_le ψ ι (ψ a))).range := fun σ _ => by
    obtain ⟨k, hk, -⟩ := hκsurj σ
    exact ⟨k, hk⟩
  have hMc : ∀ k ∈ transM ψ ι (ψ a), k * (a : MulAut V) = a * k := fun k hk => by
    obtain ⟨hkH, hkS⟩ := mem_preSub.1 hk
    have h1 : ψ (⟨k, hkH⟩ * a) = ψ (a * ⟨k, hkH⟩) := by
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.1 hkS.1
    exact congrArg Subtype.val (hψ h1)
  have hnormal : ∀ {K : Subgroup (MulAut V)}, (∀ k ∈ K, k * (a : MulAut V) = a * k) →
      K ≤ Subgroup.normalizer (Subgroup.zpowers (a : MulAut V) : Set (MulAut V)) :=
    fun hK d hd => Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun h hh => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (show Commute (a : MulAut V) d from (hK d hd).symm) j).eq)
  have hMQ := hnormal hMc
  have hMW := le_stabSub_fixV hMQ
  have hQ : IsPGroup 2 (Subgroup.zpowers (a : MulAut V)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ha2 ha1
  have hker : ∀ k : ↥(transM ψ ι (ψ a)), restrictHom ψ ι _ (transM_le ψ ι (ψ a)) k = 1 →
      ∀ w ∈ fixV (Subgroup.zpowers (a : MulAut V)), (k : MulAut V) w = w := fun k hk w _ => by
    rw [show k = 1 from hκinj (hk.trans (map_one _).symm)]
    rfl
  obtain ⟨σ₃, hσ₃⟩ := exists_isThreeCycle (m := n / 2) (by omega)
  obtain ⟨x, hx, -⟩ := hκsurj (σ₃ : Perm (Fin (n / 2)))
  have hx3 : (x : MulAut V) ^ 3 = 1 := by
    have h1 : x ^ 3 = 1 :=
      hκinj (by rw [map_pow, hx, map_one, ← hσ₃.orderOf, pow_orderOf_eq_one])
    have := congrArg Subtype.val h1
    simpa only [SubgroupClass.coe_pow, OneMemClass.coe_one] using this
  have hx1 : (x : MulAut V) ≠ 1 := fun h => hσ₃.ne_one (by
    rw [← hx, show x = 1 from Subtype.ext h, map_one])
  have hC := faithW hV (by omega) _ hκA hQ hMQ hker x
    (Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hx3)) hx1
    (by rw [hx]; exact σ₃.2) fun q hq => by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      exact (Commute.zpow_right (show Commute (x : MulAut V) a from hMc _ x.2) j).eq
  have hψWinj := autSubLift_injective (hKW := hMW) (hC := hC) hker
  have hψWA : alternatingGroup (Fin (n / 2)) ≤
      (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC).range := by
    rw [range_autSubLift]
    exact hκA
  have hBM : B ≤ transM ψ ι (ψ a) := fun b hb => by
    have hbH := (hBA.trans hA.1) hb
    refine (coe_mem_preSub (x := ⟨b, hbH⟩)).2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext (hcomm _ (hBA hb) _ haA))
    · intro y
      rw [hιΓ, hιΓ]
      exact apply_mem_orbit_iff (E := (B.subgroupOf H).map ψ) (g := ψ ⟨b, hbH⟩)
        ⟨⟨b, hbH⟩, hb, rfl⟩
  have hBΓ : ∀ b : ↥H, (b : MulAut V) ∈ B → ψ b ∈ permSetStab (Set.range ι) := fun b hb =>
    ((coe_mem_preSub (ψ := ψ) (x := b)).1 (hBM hb)).2
  have hAW := le_stabSub_fixV (hnormal fun g hg => hcomm g hg _ haA)
  have hAMW : autSub A (fixV (Subgroup.zpowers (a : MulAut V))) ≤
      autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))) := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    rcases hAB _ hg with hgB | hagB
    · exact mem_autSub.2 ⟨g, hBM hgB, rfl⟩
    · refine mem_autSub.2 ⟨⟨a * g, hAW (A.mul_mem haA hg)⟩, hBM hagB, ?_⟩
      refine MulEquiv.ext fun w => Subtype.ext ?_
      change (a : MulAut V) ((g : MulAut V) w) = (g : MulAut V) w
      exact mem_fixV_zpowers_iff.1 ((g.2 w).2 w.2)
  have hWA : commSub (fixV (Subgroup.zpowers (a : MulAut V))) A ≠ ⊥ := by
    intro hbot
    obtain ⟨b, hb, hbij⟩ := hBtr ⟨0, by omega⟩ ⟨1, by omega⟩
    have hκb : restrictHom ψ ι _ (transM_le ψ ι (ψ a)) ⟨b, hBM hb⟩ ≠ 1 := fun h => by
      have h1 := restrictHom_apply_apply (hK := transM_le ψ ι (ψ a)) ⟨(b : MulAut V), hBM hb⟩
        ⟨0, by omega⟩
      rw [h, Perm.one_apply] at h1
      have h2 := ι.injective (h1.trans hbij)
      exact absurd (congrArg Fin.val h2) (by norm_num)
    exact hκb (hC ⟨b, hBM hb⟩ fun w hw => (commSub_eq_bot_iff.1 hbot) hw _ (hBA hb))
  have hoffW := isFFStarOffender_autSub hA (fun g hg w hw => ((hAW hg) w).2 hw) hWA hAMW
  rcases hT (n / 2) (by omega) (by omega) (↥(fixV (Subgroup.zpowers (a : MulAut V))))
      (fun v => Subtype.ext (by rw [SubgroupClass.coe_pow, hV]; rfl)) _ _ hψWinj hψWA
      ⟨_, hoffW⟩ with hnat | ⟨h7, -⟩ | ⟨h8, hex⟩
  ·
    have hcount := card_altHeart_le_of_natVia hψWinj hnat hoffW
    have hBexp : IsExp2 (((autSub A (fixV (Subgroup.zpowers (a : MulAut V)))).subgroupOf
        (autSub (transM ψ ι (ψ a)) (fixV (Subgroup.zpowers (a : MulAut V))))).map
          (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)) := by
      rintro _ ⟨φ, hφ, rfl⟩
      rw [← map_mul]
      have : φ * φ = 1 := by
        obtain ⟨g, hg, hgφ⟩ := mem_autSub.1 (Subgroup.mem_subgroupOf.1 hφ)
        refine Subtype.ext ?_
        change (φ : MulAut ↥(fixV (Subgroup.zpowers (a : MulAut V)))) * φ = 1
        rw [← hgφ, ← map_mul]
        have hgg : g * g = 1 := Subtype.ext (by
          rw [Subgroup.coe_mul, ← pow_two]
          exact hsq _ hg)
        rw [hgg, map_one]
      rw [this, map_one]
    have hEB : ∀ g ∈ (B.subgroupOf H).map ψ, ∃ b' ∈ ((autSub A (fixV (Subgroup.zpowers
        (a : MulAut V)))).subgroupOf (autSub (transM ψ ι (ψ a))
          (fixV (Subgroup.zpowers (a : MulAut V))))).map
            (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC),
        ∀ j, ι (b' j) = g (ι j) := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨restrictHom ψ ι _ (transM_le ψ ι (ψ a)) ⟨b, hBM hb⟩, ?_, fun j =>
        restrictHom_apply_apply (hK := transM_le ψ ι (ψ a)) ⟨(b : MulAut V), hBM hb⟩ j⟩
      rw [← autSubLift_apply (hKW := hMW) (hC := hC)]
      exact ⟨autSubHom hMW ⟨b, hBM hb⟩,
        mem_autSub.2 ⟨Subgroup.inclusion hMW ⟨b, hBM hb⟩, hBA hb, rfl⟩, rfl⟩
    have horb : ∀ i : Fin (n / 2), 4 ≤ Nat.card (orbit (((autSub A (fixV (Subgroup.zpowers
        (a : MulAut V)))).subgroupOf (autSub (transM ψ ι (ψ a))
          (fixV (Subgroup.zpowers (a : MulAut V))))).map
            (autSubLift (restrictHom ψ ι _ (transM_le ψ ι (ψ a))) hMW hC)) i) := by
      intro i
      refine le_trans ?_ (card_orbit_le_card_orbit ι hEB i)
      have h1 : orbit ((B.subgroupOf H).map ψ) (ι i) = orbit ((B.subgroupOf H).map ψ) ω₀ :=
        MulAction.orbit_eq_iff.2 ((hιΓ (ι i)).1 ⟨i, rfl⟩)
      rw [h1, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfinΓ, hTcard]
      omega
    obtain ⟨hm8, -, -⟩ := natFF_orbit (by omega) hBexp horb hcount
    exact false_of_exitSixteenTransitive hexit (by omega) hV hψ hAlt hA htr a haA ha1 B hBA haB
      hAB ι hBΓ hBtr ht hMW hC (Or.inl hnat)
  · omega
  · exact false_of_exitSixteenTransitive hexit (by omega) hV hψ hAlt hA htr a haA ha1 B hBA haB
      hAB ι hBΓ hBtr ht hMW hC (Or.inr hex)

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
