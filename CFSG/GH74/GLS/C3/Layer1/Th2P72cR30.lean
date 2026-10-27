module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR29
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR25

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
open scoped commutatorElement

@[expose] def B_row2_autU : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* alternatingGroup (Fin 7)) ∨ HasL2Model X Odd) →
    ∀ ε σ : MulAut X, ε ^ 2 = 1 → σ ^ 2 = 1 → ε * σ = σ * ε → σ ≠ 1 → σ ≠ ε →
      ¬ Group.IsSolvable ↥(fixedSubgroup X ε) →
      ∃ u : X, u ^ 2 = 1 ∧ u ≠ 1 ∧ ε u = u ∧ σ u = u ∧
        u ∈ Subgroup.closure {x : X | ∃ c ∈ fixedSubgroup X ε, x = σ c * c⁻¹} ∧
        MulAut.conj u ∉ ({1, ε, σ, ε * σ} : Set (MulAut X))

@[expose] def B_row2_autZ : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (Nonempty (X ≃* alternatingGroup (Fin 7)) ∨ HasL2Model X (fun r => Odd r ∧ r ≠ 9)) →
    ∀ Eb Pb : Subgroup (MulAut X), CFSG.IsElementaryAbelian 2 ↥Eb → Nat.card ↥Eb = 4 →
      (∀ ε ∈ Eb, ε ≠ 1 → Group.IsSolvable ↥(fixedSubgroup X ε)) →
      (∃ n : ℕ, 3 ≤ n ∧ Nonempty (↥Pb ≃* DihedralGroup (2 ^ (n - 1)))) →
      (∀ p ∈ Pb, ∀ e ∈ Eb, p * e = e * p) → False

theorem b_row2_stageB_of_aut (hrank : B_ivk_L29_rank) (hU : B_row2_autU) (hZ : B_row2_autZ) :
    B_row2_stageB := by
  intro G _ _ hG v t z L P E hv2 ht2 hz2 hL hunb hX hLN hEel hE2 htE hEz hEv hPdih hzP hzPc hPE
    hPEbot he₁ hzN hzL hmax
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hEc, hEsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hEel
  have hcardE : Nat.card E = 4 := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hEel, hE2]
    norm_num
  have hEn : ∀ x ∈ E, x ∈ normalizer (L : Set G) := fun x hx =>
    hLN x (mem_centralizer_singleton_iff.2 (hEv x hx))
  obtain ⟨e₁, he₁E, he₁1, hve⟩ := he₁
  obtain ⟨n, hn3, ⟨φ⟩⟩ := hPdih
  have hz1 : z * z = 1 := by
    have : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
    rwa [sq] at this
  have hPv : ∀ p ∈ P, p * v = v * p := by
    intro p hp
    rw [hve]
    calc p * (z * e₁) = (p * z) * e₁ := by group
      _ = (z * p) * e₁ := by rw [hzPc p hp]
      _ = z * (p * e₁) := by group
      _ = z * (e₁ * p) := by rw [hPE p hp e₁ he₁E]
      _ = z * e₁ * p := by group
  have hPn : ∀ p ∈ P, p ∈ normalizer (L : Set G) := fun p hp =>
    hLN p (mem_centralizer_singleton_iff.2 (hPv p hp))
  have hρz : rhoL L z ≠ 1 := fun h => hzL ((rhoL_eq_one_iff hzN).1 h)
  have hρz2 : rhoL L z * rhoL L z = 1 := by
    rw [← rhoL_mul hzN hzN, hz1, rhoL_one]
  have hvN : v ∈ normalizer (L : Set G) := hLN v (mem_centralizer_singleton_iff.2 rfl)
  have hρv : rhoL L v = 1 := by
    rw [rhoL_eq_one_iff hvN]
    refine ⟨hvN, TwoThin.mem_normalizer_pPrimeCoreOf hvN, fun k hk => ?_⟩
    have hkv : k * v = v * k := mem_centralizer_singleton_iff.1 (hL.1 hk)
    have : ⁅k, v⁆ = 1 := by
      rw [commutatorElement_def, hkv]
      group
    rw [this]
    exact one_mem _
  have hρe₁ : rhoL L e₁ = rhoL L z := by
    have h1 : rhoL L v = rhoL L z * rhoL L e₁ := by
      rw [hve]
      exact rhoL_mul hzN (hEn e₁ he₁E)
    rw [hρv] at h1
    have h2 : rhoL L e₁ = (rhoL L z)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
    rw [h2]
    exact inv_eq_of_mul_eq_one_right hρz2
  have hSimple : IsSimpleGroup (kBar L) := isSimple_of_u2 hX
  have hNS : ¬ Group.IsSolvable (kBar L) := by
    intro hs
    have hcomm : ∀ a b : kBar L, a * b = b * a :=
      (IsSimpleGroup.comm_iff_isSolvable (G := kBar L)).2 hs
    obtain ⟨a, ha⟩ := exists_ne (1 : kBar L)
    exact ha ((centerless_two_le_of_u2 hL hX).1 a (fun b => hcomm a b))
  have hfixone : ¬ Group.IsSolvable ↥(fixedSubgroup (kBar L) (1 : MulAut (kBar L))) := by
    intro hs
    have htop : fixedSubgroup (kBar L) (1 : MulAut (kBar L)) = ⊤ := by
      ext k
      simp [fixedSubgroup]
    let e : kBar L ≃* ↥(fixedSubgroup (kBar L) (1 : MulAut (kBar L))) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    exact hNS (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  have hpair : ∀ e e' : G, e ∈ E → e' ∈ E → e ≠ 1 → e' ≠ 1 → e' ≠ e → rhoL L e' ≠ 1 →
      rhoL L e' ≠ rhoL L e → ¬ Group.IsSolvable ↥(fixedSubgroup (kBar L) (rhoL L e)) → False := by
    intro e e' he he' he1 he'1 hee' hρe' hρee' hns
    obtain ⟨N, hEN, hNinv, hNmax⟩ := hmax e he he1
    have hall := mem_four_of_card hcardE he he' he1 he'1 (Ne.symm hee') (hEsq e he)
    have hε2 : rhoL L e ^ 2 = 1 := by
      rw [sq, ← rhoL_mul (hEn e he) (hEn e he), hEsq e he, rhoL_one]
    have hσ2 : rhoL L e' ^ 2 = 1 := by
      rw [sq, ← rhoL_mul (hEn e' he') (hEn e' he'), hEsq e' he', rhoL_one]
    have hεσ : rhoL L e * rhoL L e' = rhoL L e' * rhoL L e := by
      rw [← rhoL_mul (hEn e he) (hEn e' he'), ← rhoL_mul (hEn e' he') (hEn e he), hEc e he e' he']
    obtain ⟨u, hu2, hu1, hεu, hσu, hucl, hconj⟩ :=
      hU (kBar L) hX (rhoL L e) (rhoL L e') hε2 hσ2 hεσ hρe' hρee' hns
    refine key_max hEel hEn he he1 he' hEN hNinv hNmax hu2 hu1 hucl ?_ ?_
    · intro x hx
      rcases hall x hx with h | h | h | h
      · rw [h, rhoL_one]
        rfl
      · rw [h]
        exact hεu
      · rw [h]
        exact hσu
      · rw [h, rhoL_mul (hEn e he) (hEn e' he')]
        show rhoL L e (rhoL L e' u) = u
        rw [hσu, hεu]
    · intro x hx hxu
      apply hconj
      rw [← hxu]
      rcases hall x hx with h | h | h | h
      · rw [h, rhoL_one]
        exact Set.mem_insert _ _
      · rw [h]
        exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · rw [h]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · rw [h, rhoL_mul (hEn e he) (hEn e' he')]
        exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
          (Set.mem_singleton _)))
  have hker : ∀ e ∈ E, rhoL L e = 1 → e = 1 := by
    intro e he hρ
    by_contra he1
    have hρ1 : rhoL L e₁ ≠ 1 := by
      rw [hρe₁]
      exact hρz
    have hne : e₁ ≠ e := by
      intro h
      rw [h] at hρ1
      exact hρ1 hρ
    refine hpair e e₁ he he₁E he1 he₁1 hne hρ1 (by rw [hρ]; exact hρ1) ?_
    rw [hρ]
    exact hfixone
  have hinjE : ∀ x ∈ E, ∀ y ∈ E, rhoL L x = rhoL L y → x = y := by
    intro x hx y hy h
    have h1 : rhoL L (x * y⁻¹) = 1 := by
      rw [rhoL_mul (hEn x hx) (inv_mem (hEn y hy)), rhoL_inv (hEn y hy), h, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hker _ (E.mul_mem hx (E.inv_mem hy)) h1)
  have hsolv : ∀ e ∈ E, e ≠ 1 → Group.IsSolvable ↥(fixedSubgroup (kBar L) (rhoL L e)) := by
    intro e he he1
    by_contra hns
    have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hEsq e he) he1
    obtain ⟨e', he', he'1, hee'⟩ := exists_third hcardE he2
    refine hpair e e' he he' he1 he'1 hee' ?_ ?_ hns
    · intro h
      exact he'1 (hker e' he' h)
    · intro h
      exact hee' (hinjE e' he' e he h)
  by_cases h9 : HasL2Model (kBar L) (fun q => q = 9)
  ·
    exfalso
    obtain ⟨hZc, w, hwP, hww, hw1, hwz⟩ := central_of_dihedral hn3 φ hzP hz2 hzPc
    have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hww) hw1
    have hwE : ∀ f ∈ E, f * w = w * f := fun f hf => (hPE w hwP f hf).symm
    have hAB : ∀ a ∈ E, ∀ b ∈ zpowers w, a * b = b * a := by
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right (show Commute a w from hwE a ha) k).eq
    have hAel : CFSG.IsElementaryAbelian 2 ↥(E ⊔ zpowers w) :=
      isElementaryAbelian_sup_zpowers hEel hww hwE
    have hAn : E ⊔ zpowers w ≤ NxK v L := by
      refine sup_le ?_ ?_
      · intro x hx
        exact ⟨mem_centralizer_singleton_iff.2 (hEv x hx), hEn x hx⟩
      · rw [Subgroup.zpowers_le]
        exact ⟨mem_centralizer_singleton_iff.2 (hPv w hwP), hPn w hwP⟩
    have htA : t ∈ E ⊔ zpowers w := Subgroup.mem_sup_left htE
    have hbound := hrank G hG v t L hunb h9 (E ⊔ zpowers w) hAn hAel htA
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    have hwnorm : zpowers w ≤ normalizer (E : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro g
      constructor
      · intro hg
        have : w * g * w⁻¹ = g := by
          calc w * g * w⁻¹ = (g * w) * w⁻¹ := by rw [← hwE g hg]
            _ = g := by group
        rw [this]
        exact hg
      · intro hg
        set y : G := w * g * w⁻¹ with hy
        have h2 : w * y * w⁻¹ = y := by
          calc w * y * w⁻¹ = (y * w) * w⁻¹ := by rw [← hwE y hg]
            _ = y := by group
        have h3 : w * y * w⁻¹ = g := by
          calc w * y * w⁻¹ = (w * w) * g * (w⁻¹ * w⁻¹) := by rw [hy]; group
            _ = g := by rw [hwi, hww]; group
        rw [← h3, h2]
        exact hg
    have hcardA : Nat.card ↥(E ⊔ zpowers w) = 8 := by
      have hprod := Th2.HY.card_sup_mul_card_inf_of_le_normalizer hwnorm
      have hinf : zpowers w ⊓ E = ⊥ := by
        refine eq_bot_iff.2 fun x hx => ?_
        rcases mem_zpowers_two hw2 hx.1 with h | h
        · rw [h]
          exact one_mem _
        · exfalso
          have : w ∈ P ⊓ E := ⟨hwP, h ▸ hx.2⟩
          rw [hPEbot, Subgroup.mem_bot] at this
          exact hw1 this
      rw [hinf, Subgroup.card_bot, Nat.card_zpowers, hw2, hcardE, sup_comm] at hprod
      omega
    have hbot : (E ⊔ zpowers w) ⊓ CxK v L = ⊥ := by
      refine eq_bot_iff.2 fun a ha => ?_
      obtain ⟨haA, haC⟩ := ha
      obtain ⟨f, hf, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hAB haA
      have haN : f * b ∈ normalizer (L : Set G) := haC.2.1
      have hρa : rhoL L (f * b) = 1 := (rhoL_eq_one_iff haN).2 haC.2
      rcases mem_zpowers_two hw2 hb with hb1 | hbw
      · rw [hb1, mul_one] at hρa ⊢
        rw [hker f hf hρa]
        exact one_mem _
      · exfalso
        rw [hbw, rhoL_mul (hEn f hf) (hPn w hwP)] at hρa
        have hρw : rhoL L w = (rhoL L f)⁻¹ := eq_inv_of_mul_eq_one_right hρa
        have hwcen : ∀ p ∈ P, w * p = p * w := by
          intro p hp
          apply rhoL_injOn_P hn3 φ hPn hzP hz2 hzPc hρz (P.mul_mem hwP hp) (P.mul_mem hp hwP)
          rw [rhoL_mul (hPn w hwP) (hPn p hp), rhoL_mul (hPn p hp) (hPn w hwP), hρw]
          have hfp : rhoL L f * rhoL L p = rhoL L p * rhoL L f := by
            rw [← rhoL_mul (hEn f hf) (hPn p hp), ← rhoL_mul (hPn p hp) (hEn f hf),
              (hPE p hp f hf).symm]
          exact (Commute.inv_left (show Commute (rhoL L f) (rhoL L p) from hfp)).eq
        rcases hZc w hwP hwcen with h | h
        · exact hw1 h
        · exact hwz h
    rw [hbot, Subgroup.card_bot, hcardA] at hbound
    omega
  · have hX' : Nonempty (kBar L ≃* alternatingGroup (Fin 7)) ∨
        HasL2Model (kBar L) (fun r => Odd r ∧ r ≠ 9) := by
      rcases hX with hA | ⟨p, f, hp, hf, hodd, hmod⟩
      · exact Or.inl hA
      · exact Or.inr ⟨p, f, hp, hf, ⟨hodd, fun h => h9 ⟨p, f, hp, hf, h, hmod⟩⟩, hmod⟩
    let ρE : ↥E →* MulAut (kBar L) :=
      (barAct L).comp (Subgroup.inclusion (fun x hx => hEn x hx))
    have hρE : ∀ x : ↥E, ρE x = rhoL L x := fun x => (rhoL_of_mem (hEn x x.2)).symm
    have hmemE : ∀ y, y ∈ ρE.range ↔ ∃ x ∈ E, rhoL L x = y := by
      intro y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, (hρE x).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, hρE ⟨x, hx⟩⟩
    have hEbel : CFSG.IsElementaryAbelian 2 ↥ρE.range := by
      apply C3.Layer1.Back.isElementaryAbelian_of_forall
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := (hmemE a).1 ha
        obtain ⟨y, hy, rfl⟩ := (hmemE b).1 hb
        rw [← rhoL_mul (hEn x hx) (hEn y hy), ← rhoL_mul (hEn y hy) (hEn x hx), hEc x hx y hy]
      · intro a ha
        obtain ⟨x, hx, rfl⟩ := (hmemE a).1 ha
        rw [← rhoL_mul (hEn x hx) (hEn x hx), hEsq x hx, rhoL_one]
    have hinjρE : Function.Injective ρE := by
      intro x y h
      apply Subtype.ext
      exact hinjE x.1 x.2 y.1 y.2 (by rw [← hρE x, ← hρE y]; exact h)
    have hEbcard : Nat.card ↥ρE.range = 4 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinjρE).toEquiv]
      exact hcardE
    have hEbsolv : ∀ ε ∈ ρE.range, ε ≠ 1 → Group.IsSolvable ↥(fixedSubgroup (kBar L) ε) := by
      intro ε hε hε1
      obtain ⟨x, hx, rfl⟩ := (hmemE ε).1 hε
      have hx1 : x ≠ 1 := by
        rintro rfl
        exact hε1 (rhoL_one L)
      exact hsolv x hx hx1
    let ρP : ↥P →* MulAut (kBar L) :=
      (barAct L).comp (Subgroup.inclusion (fun p hp => hPn p hp))
    have hρP : ∀ p : ↥P, ρP p = rhoL L p := fun p => (rhoL_of_mem (hPn p p.2)).symm
    have hmemP : ∀ y, y ∈ ρP.range ↔ ∃ p ∈ P, rhoL L p = y := by
      intro y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.2, (hρP x).symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, hρP ⟨x, hx⟩⟩
    have hinjρP : Function.Injective ρP := by
      intro p q h
      apply Subtype.ext
      exact rhoL_injOn_P hn3 φ hPn hzP hz2 hzPc hρz p.2 q.2 (by rw [← hρP p, ← hρP q]; exact h)
    have hPbdih : ∃ m : ℕ, 3 ≤ m ∧ Nonempty (↥ρP.range ≃* DihedralGroup (2 ^ (m - 1))) :=
      ⟨n, hn3, ⟨(MonoidHom.ofInjective hinjρP).symm.trans φ⟩⟩
    have hcommPE : ∀ a ∈ ρP.range, ∀ b ∈ ρE.range, a * b = b * a := by
      intro a ha b hb
      obtain ⟨p, hp, rfl⟩ := (hmemP a).1 ha
      obtain ⟨x, hx, rfl⟩ := (hmemE b).1 hb
      rw [← rhoL_mul (hPn p hp) (hEn x hx), ← rhoL_mul (hEn x hx) (hPn p hp), hPE p hp x hx]
    exact hZ (kBar L) hX' ρE.range ρP.range hEbel hEbcard hEbsolv hPbdih hcommPE


end CFSG.GH74.GLS
