module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma138
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Rank
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.OrbitBound

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims138

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open scoped commutatorElement

theorem inputI181_of_schreier
    (hS : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier) :
    Lemma138.InputI181 := by
  intro X _ _ p hp hK Q hQ
  have hKt : CFSG.Open.IsKGroup ↥(⊤ : Subgroup X) :=
    CFSG.KCore.KGroupAllSimple.kGroupNonab (hK.subgroup ⊤)
  have h := CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPLayer_inf_centralizer_le hS hKt hp
    (le_top : Q ≤ ⊤) hQ
  rwa [top_inf_eq] at h

theorem inputI181_holds
    : Lemma138.InputI181 :=
  inputI181_of_schreier CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds

theorem inputI113p_of_inputs (h : CFSG.LocalAnalysis.GLTheoremB.Input11_3) :
    Lemma138.InputI113p := by
  intro X _ _ hK p hp hp2 B hB L hL hnL
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ := h X (CFSG.KCore.KGroupAllSimple.kGroupNonab hK) p hp hp2 B hB L hL hnL
  by_contra hndvd
  apply hZ
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L))) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hle : Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) ≤
      CFSG.pPrimeCore p (↥L ⧸ GLAPPrimeCore p ↥L) :=
    le_sSup ⟨inferInstance, hcop⟩
  have hbot : CFSG.pPrimeCore p (↥L ⧸ GLAPPrimeCore p ↥L) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  rw [hbot] at hle
  exact le_bot_iff.1 hle

theorem inputI113p_of_I112 (h : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I112) :
    Lemma138.InputI113p :=
  inputI113p_of_inputs (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_3_of_I112 h)

theorem inputI113p_of_tables (T : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (TL : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableL2) : Lemma138.InputI113p :=
  inputI113p_of_inputs (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.input11_3_of_tables T TL)

section Rank

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem card_sup_mul_card_inf {A N : Subgroup X} (hAN : A ≤ Subgroup.normalizer (N : Set X)) :
    Nat.card (A ⊔ N : Subgroup X) * Nat.card (A ⊓ N : Subgroup X) = Nat.card A * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient A N hAN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (A ⊔ N))
  have h3 : Nat.card (N.subgroupOf A) = Nat.card (A ⊓ N : Subgroup X) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (A ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem elem_comm {E : Subgroup X} (hE : IsElemAbelian p E) {a b : X} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  have := hE.1.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩
  exact congrArg (fun x : ↥E => (x : X)) this

theorem card_eq_pow_pRank (hp : p.Prime) {E : Subgroup X} (hE : IsElemAbelian p E) :
    Nat.card E = p ^ CFSG.Open.pRank p E := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  have h1 : k ≤ CFSG.Open.pRank p E := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hE hk
  have h2 : CFSG.Open.pRank p E ≤ k := CFSG.SectionRank.pRank_le hp.one_lt fun F hFE _ =>
    hk ▸ Subgroup.card_le_of_le hFE
  rw [hk, le_antisymm h1 h2]

theorem pRank_le_one_of_card_lt (hp : p.Prime) {H : Subgroup X} (hH : Nat.card H < p ^ 2) :
    CFSG.Open.pRank p H ≤ 1 := by
  obtain ⟨E, hEH, -, hE⟩ := CFSG.SectionRank.exists_pRank hp.one_lt H
  have h1 : p ^ CFSG.Open.pRank p H < p ^ 2 :=
    lt_of_le_of_lt (hE ▸ Subgroup.card_le_of_le hEH) hH
  have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h1
  omega

theorem eq_gamma_of_two_le_pRank {J B : Subgroup X}
    (h2 : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (J : Set X))) :
    J = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      J ⊓ Subgroup.normalizer (U : Set X) := by
  refine le_antisymm ?_ (iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left)
  have hJC : J ≤ Subgroup.centralizer
      ((B ⊓ Subgroup.centralizer (J : Set X) : Subgroup X) : Set X) :=
    Subgroup.le_centralizer_iff.2 inf_le_right
  have hJN : J ≤ Subgroup.normalizer
      ((B ⊓ Subgroup.centralizer (J : Set X) : Subgroup X) : Set X) :=
    hJC.trans (Subgroup.centralizer_le_normalizer _)
  exact le_iSup_of_le (B ⊓ Subgroup.centralizer (J : Set X)) (le_iSup_of_le inf_le_left
    (le_iSup_of_le h2 (le_inf le_rfl hJN)))

variable {J B : Subgroup X}

theorem card_split (hB : IsElemAbelian p B)
    (hsplit : (B ⊓ J) ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) = B)
    (hint : (B ⊓ J) ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥) :
    Nat.card B = Nat.card ↥(B ⊓ J) * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set X)) := by
  have hN : B ⊓ J ≤
      Subgroup.normalizer ((B ⊓ Subgroup.centralizer (J : Set X) : Subgroup X) : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact elem_comm hB (Subgroup.mem_inf.1 hy).1 (Subgroup.mem_inf.1 hx).1
  have h := card_sup_mul_card_inf hN
  rw [hsplit, hint, Subgroup.card_bot, mul_one] at h
  exact h

theorem pRank_split (hp : p.Prime) (hB : IsElemAbelian p B)
    (hsplit : (B ⊓ J) ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) = B)
    (hint : (B ⊓ J) ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥) :
    CFSG.Open.pRank p B = CFSG.Open.pRank p (B ⊓ J) +
      CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (J : Set X)) := by
  have h := card_split hB hsplit hint
  rw [card_eq_pow_pRank hp hB,
    card_eq_pow_pRank hp (CFSG.Open.IsElemAbelian.mono hB inf_le_left),
    card_eq_pow_pRank hp (CFSG.Open.IsElemAbelian.mono hB inf_le_left), ← pow_add] at h
  exact Nat.pow_right_injective hp.two_le h

theorem card_le_of_split (hp : p.Prime) (hB : IsElemAbelian p B)
    (hsplit : (B ⊓ J) ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) = B)
    (hint : (B ⊓ J) ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥)
    (hrk : CFSG.Open.pRank p (B ⊓ J) = CFSG.Open.pRank p J) :
    ∀ A : Subgroup X, A ≤ B ⊔ J → IsElemAbelian p A → Nat.card A ≤ Nat.card B := by
  intro A hAle hA
  set C : Subgroup X := B ⊓ Subgroup.centralizer (J : Set X) with hCdef
  have hCJ : C ≤ Subgroup.normalizer (J : Set X) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hBJ : B ⊔ J = C ⊔ J := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      calc B = (B ⊓ J) ⊔ C := hsplit.symm
        _ ≤ C ⊔ J := sup_le (inf_le_right.trans le_sup_right) le_sup_left
    · exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hCJbot : C ⊓ J = ⊥ := by
    refine le_bot_iff.1 ?_
    rw [← hint]
    intro x hx
    obtain ⟨hxC, hxJ⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hxC).1, hxJ⟩, hxC⟩
  have hCJcard : Nat.card ↥(C ⊔ J) = Nat.card C * Nat.card J := by
    have h := card_sup_mul_card_inf hCJ
    rwa [hCJbot, Subgroup.card_bot, mul_one] at h
  have hAN : A ≤ Subgroup.normalizer (J : Set X) :=
    (hAle.trans hBJ.le).trans (sup_le hCJ Subgroup.le_normalizer)
  have hAJ := card_sup_mul_card_inf hAN
  have hAJle : Nat.card ↥(A ⊔ J) ≤ Nat.card ↥(C ⊔ J) :=
    Subgroup.card_le_of_le (sup_le (hAle.trans hBJ.le) le_sup_right)
  have hAJrk : Nat.card ↥(A ⊓ J) ≤ p ^ CFSG.Open.pRank p J := by
    have hAJel : IsElemAbelian p (A ⊓ J) := CFSG.Open.IsElemAbelian.mono hA inf_le_left
    rw [card_eq_pow_pRank hp hAJel]
    exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right)
  have hBcard : Nat.card B = p ^ CFSG.Open.pRank p J * Nat.card C := by
    rw [card_split hB hsplit hint,
      card_eq_pow_pRank hp (CFSG.Open.IsElemAbelian.mono hB inf_le_left), hrk]
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have key : Nat.card A * Nat.card J ≤ (p ^ CFSG.Open.pRank p J * Nat.card C) * Nat.card J := by
    rw [← hAJ]
    calc Nat.card ↥(A ⊔ J) * Nat.card ↥(A ⊓ J)
        ≤ Nat.card ↥(C ⊔ J) * p ^ CFSG.Open.pRank p J := Nat.mul_le_mul hAJle hAJrk
      _ = (p ^ CFSG.Open.pRank p J * Nat.card C) * Nat.card J := by rw [hCJcard]; ring
  rw [hBcard]
  exact Nat.le_of_mul_le_mul_right key hJpos

end Rank

section Alt

open Equiv Equiv.Perm MulAction

theorem le_pRank_of_mulEquiv_alt {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {J : Subgroup X} {n : ℕ} (e : ↥J ≃* alternatingGroup (Fin n)) :
    n / p ≤ CFSG.Open.pRank p J := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨emb⟩ : Nonempty ((Fin (n / p) × ZMod p) ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by
      simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card]
      exact Nat.div_mul_le_self n p)
  let Φ : Multiplicative (Fin (n / p) → ZMod p) →* Perm (Fin n) :=
    (Equiv.Perm.extendDomainHom emb.toEquivRange).comp GL83.PiGen.shiftHom
  have hΦ : Function.Injective Φ :=
    (Equiv.Perm.extendDomainHom_injective _).comp GL83.PiGen.shiftHom_injective
  have hpow : ∀ u : Multiplicative (Fin (n / p) → ZMod p), u ^ p = 1 := by
    intro u
    rw [← ofAdd_toAdd u, ← ofAdd_nsmul]
    have : p • Multiplicative.toAdd u = 0 := by
      ext i
      simp
    rw [this]
    rfl
  have hE₁el : IsElemAbelian p Φ.range := by
    refine ⟨inferInstance, ?_⟩
    rintro _ ⟨u, rfl⟩
    rw [← map_pow, hpow, map_one]
  have hE₁A : Φ.range ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨u, rfl⟩
    exact GL83.PiGen.mem_alternatingGroup_of_pow_eq_one hpodd (by rw [← map_pow, hpow, map_one])
  have hcard1 : Nat.card Φ.range = p ^ (n / p) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hEJ : ((Φ.range.subgroupOf (alternatingGroup (Fin n))).map e.symm.toMonoidHom).map
      J.subtype ≤ J := Subgroup.map_subtype_le _
  have hEel : IsElemAbelian p (((Φ.range.subgroupOf (alternatingGroup (Fin n))).map
      e.symm.toMonoidHom).map J.subtype) :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.SectionRank.isElemAbelian_map
      (CFSG.Open.IsElemAbelian.subgroupOf hE₁el _) _) _
  have hEcard : Nat.card (((Φ.range.subgroupOf (alternatingGroup (Fin n))).map
      e.symm.toMonoidHom).map J.subtype) = p ^ (n / p) := by
    rw [Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁A).toEquiv, hcard1]
  exact CFSG.SectionRank.le_pRank hp.one_lt hEJ hEel hEcard

variable {n p : ℕ}

@[expose] def pairStab (R : Subgroup (Perm (Fin n))) (ω ω' : Fin n) : Subgroup (Perm (Fin n)) :=
  GL83.PiGen.stabIn R ω ⊓ GL83.PiGen.stabIn R ω'

theorem pairStab_le (R : Subgroup (Perm (Fin n))) (ω ω' : Fin n) : pairStab R ω ω' ≤ R :=
  inf_le_left.trans (GL83.PiGen.stabIn_le R ω)

theorem mem_fixSet_pairStab_left (R : Subgroup (Perm (Fin n))) (ω ω' : Fin n) :
    ω ∈ GL83.PiGen.fixSet (pairStab R ω ω') :=
  GL83.PiGen.fixSet_anti inf_le_left (GL83.PiGen.mem_fixSet_stabIn R ω)

theorem mem_fixSet_pairStab_right (R : Subgroup (Perm (Fin n))) (ω ω' : Fin n) :
    ω' ∈ GL83.PiGen.fixSet (pairStab R ω ω') :=
  GL83.PiGen.fixSet_anti inf_le_right (GL83.PiGen.mem_fixSet_stabIn R ω')

theorem card_orbit_le_of_rank (hp : p.Prime) (hp3 : 3 ≤ p) {R : Subgroup (Perm (Fin n))}
    (hR : IsElemAbelian p R) {r : ℕ} (hRcard : Nat.card R = p ^ r) (hnr : n / p ≤ r)
    (ω : Fin n) : Nat.card (orbit R ω) ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, hs⟩ := (CFSG.Open.IsElemAbelian.isPGroup hR).card_orbit ω
  by_contra hlt
  have hs2 : 2 ≤ s := by
    by_contra h
    interval_cases s
    · rw [hs] at hlt
      simp at hlt
      omega
    · rw [hs] at hlt
      simp at hlt
  have hb := GL83.PiGen.card_le_orbit_bound hR ω hs
  rw [hRcard, ← pow_add, Fintype.card_fin] at hb
  have h1 := (Nat.pow_le_pow_iff_right hp.one_lt).1 hb
  have hsn : p ^ s ≤ n := by
    have h := Nat.card_le_card_of_injective (Subtype.val : (orbit R ω) → Fin n)
      Subtype.val_injective
    rwa [hs, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hps : p ^ (s' + 1) = p * p ^ s' := by rw [pow_succ, mul_comm]
  rw [hps, Nat.sub_mul_div] at h1
  have hle : p ^ s' ≤ n / p := (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm, ← hps]; exact hsn)
  have h3 : s' + 2 ≤ 3 ^ s' := GL83.PiGen.three_pow_ge s' (by omega)
  have h4 : 3 ^ s' ≤ p ^ s' := Nat.pow_le_pow_left hp3 s'
  omega

theorem card_le_pairStab {R : Subgroup (Perm (Fin n))}
    (hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) (horb : ∀ ω : Fin n, Nat.card (orbit R ω) ≤ p)
    (ω ω' : Fin n) : Nat.card R ≤ p ^ 2 * Nat.card (pairStab R ω ω') := by
  have h1 := GL83.PiGen.card_mul_card_stabIn R ω
  have h2 := GL83.PiGen.card_mul_card_stabIn R ω'
  have hN : GL83.PiGen.stabIn R ω ≤
      Subgroup.normalizer (GL83.PiGen.stabIn R ω' : Set (Perm (Fin n))) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hRcomm y (GL83.PiGen.stabIn_le R _ hy) x (GL83.PiGen.stabIn_le R _ hx)
  have h3 := card_sup_mul_card_inf hN
  have h4 : Nat.card ↥(GL83.PiGen.stabIn R ω ⊔ GL83.PiGen.stabIn R ω') ≤ Nat.card R :=
    Subgroup.card_le_of_le (sup_le (GL83.PiGen.stabIn_le R _) (GL83.PiGen.stabIn_le R _))
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have key : Nat.card R * Nat.card R ≤ (p ^ 2 * Nat.card (pairStab R ω ω')) * Nat.card R := by
    calc Nat.card R * Nat.card R
        = (Nat.card (orbit R ω) * Nat.card (GL83.PiGen.stabIn R ω)) *
          (Nat.card (orbit R ω') * Nat.card (GL83.PiGen.stabIn R ω')) := by rw [← h1, ← h2]
      _ ≤ (p * Nat.card (GL83.PiGen.stabIn R ω)) * (p * Nat.card (GL83.PiGen.stabIn R ω')) := by
          gcongr
          · exact horb ω
          · exact horb ω'
      _ = p ^ 2 * (Nat.card (GL83.PiGen.stabIn R ω) * Nat.card (GL83.PiGen.stabIn R ω')) := by
          ring
      _ = p ^ 2 * (Nat.card ↥(GL83.PiGen.stabIn R ω ⊔ GL83.PiGen.stabIn R ω') *
          Nat.card (pairStab R ω ω')) := by rw [← h3]; rfl
      _ ≤ p ^ 2 * (Nat.card R * Nat.card (pairStab R ω ω')) := by gcongr
      _ = (p ^ 2 * Nat.card (pairStab R ω ω')) * Nat.card R := by ring
  exact Nat.le_of_mul_le_mul_right key hRpos

theorem alternatingGroup_le_of_pairs {R : Subgroup (Perm (Fin n))}
    (hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (horb3 : ∀ ω : Fin n, ω ∉ GL83.PiGen.fixSet R → 3 ≤ (orbit R ω).ncard)
    {ω₀ : Fin n} (hω₀ : ω₀ ∉ GL83.PiGen.fixSet R) {Γ' : Subgroup (Perm (Fin n))}
    (hΓ : ∀ ω ω' : Fin n, ω ∉ GL83.PiGen.fixSet R →
      GL83.altOn (GL83.PiGen.fixSet (pairStab R ω ω')) ≤ Γ') :
    alternatingGroup (Fin n) ≤ Γ' := by
  classical
  haveI : Nonempty (Fin n) := ⟨ω₀⟩
  let S : {q : Fin n × Fin n // q.1 ∉ GL83.PiGen.fixSet R} → Set (Fin n) := fun i =>
    GL83.PiGen.fixSet (pairStab R i.1.1 i.1.2)
  have horbS : ∀ i, orbit R i.1.1 ⊆ S i := by
    intro i x hx
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    have hvω : v i.1.1 = i.1.1 := mem_fixSet_pairStab_left R i.1.1 i.1.2 v hv
    exact CFSG.AGLEmbedding.apply_apply_eq_of_commute hRcomm (pairStab_le R _ _ hv) g.2 hvω
  have hS3 : ∀ i, 3 ≤ (S i).ncard := fun i =>
    (horb3 i.1.1 i.2).trans (Set.ncard_le_ncard (horbS i) (Set.toFinite _))
  have hcover : (⋃ i, S i) = Set.univ :=
    Set.eq_univ_of_forall fun x =>
      Set.mem_iUnion.2 ⟨⟨(ω₀, x), hω₀⟩, mem_fixSet_pairStab_right R ω₀ x⟩
  have hconn : ∀ i j, Relation.ReflTransGen (fun a b => (S a ∩ S b).Nonempty) i j := by
    intro i j
    refine Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (b := ⟨(i.1.1, j.1.1), i.2⟩) ?_)
      (Relation.ReflTransGen.single ?_)
    · exact ⟨i.1.1, mem_fixSet_pairStab_left R _ _, mem_fixSet_pairStab_left R _ _⟩
    · exact ⟨j.1.1, mem_fixSet_pairStab_right R _ _, mem_fixSet_pairStab_left R _ _⟩
  rw [← GL83.iSup_altOn_eq_alternatingGroup hS3 hcover hconn]
  exact iSup_le fun i => hΓ i.1.1 i.1.2 i.2

theorem eq_gamma_of_isAltType {X : Type} [Group X] [Finite X] (hp : p.Prime) (hp2 : p ≠ 2)
    {J B : Subgroup X} (hA : IsAltType n J) (hB : IsElemAbelian p B)
    (hsplit : (B ⊓ J) ⊔ (B ⊓ Subgroup.centralizer (J : Set X)) = B)
    (hint : (B ⊓ J) ⊓ (B ⊓ Subgroup.centralizer (J : Set X)) = ⊥)
    (hrk : CFSG.Open.pRank p (B ⊓ J) = CFSG.Open.pRank p J) (hB4 : 4 ≤ CFSG.Open.pRank p B) :
    J = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      J ⊓ Subgroup.normalizer (U : Set X) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  by_cases hc2 : 2 ≤ CFSG.Open.pRank p (B ⊓ Subgroup.centralizer (J : Set X))
  · exact eq_gamma_of_two_le_pRank hc2
  have hsum := pRank_split hp hB hsplit hint
  have hr3 : 3 ≤ CFSG.Open.pRank p (B ⊓ J) := by omega
  obtain ⟨e⟩ := hA
  have hnr : n / p ≤ CFSG.Open.pRank p (B ⊓ J) := hrk ▸ le_pRank_of_mulEquiv_alt hp hp2 e
  let φ : ↥J →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := (Subgroup.subtype_injective _).comp e.injective
  have hBJel : IsElemAbelian p (B ⊓ J) := CFSG.Open.IsElemAbelian.mono hB inf_le_left
  have hRel : IsElemAbelian p (((B ⊓ J).subgroupOf J).map φ) :=
    CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hBJel J) φ
  have hRcard : Nat.card (((B ⊓ J).subgroupOf J).map φ) = p ^ CFSG.Open.pRank p (B ⊓ J) := by
    rw [Subgroup.card_map_of_injective hφ,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,
      card_eq_pow_pRank hp hBJel]
  have hRcomm : ∀ x ∈ ((B ⊓ J).subgroupOf J).map φ, ∀ y ∈ ((B ⊓ J).subgroupOf J).map φ,
      x * y = y * x := fun x hx y hy => elem_comm hRel hx hy
  have horb := card_orbit_le_of_rank hp hp3 hRel hRcard hnr
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Fin n, ω₀ ∉ GL83.PiGen.fixSet (((B ⊓ J).subgroupOf J).map φ) := by
    by_contra h
    push Not at h
    have hbot : ((B ⊓ J).subgroupOf J).map φ = ⊥ :=
      CFSG.AGLEmbedding.eq_bot_of_forall_apply_eq fun g hg a => (h a) g hg
    have h1 : Nat.card (((B ⊓ J).subgroupOf J).map φ) = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hRcard] at h1
    rcases Nat.pow_eq_one.1 h1 with h | h
    · exact hp.one_lt.ne' h
    · omega
  have horb3 : ∀ ω : Fin n, ω ∉ GL83.PiGen.fixSet (((B ⊓ J).subgroupOf J).map φ) →
      3 ≤ (orbit (((B ⊓ J).subgroupOf J).map φ) ω).ncard := by
    intro ω hω
    obtain ⟨s, hs⟩ := (CFSG.Open.IsElemAbelian.isPGroup hRel).card_orbit ω
    have hle := horb ω
    rw [GL83.PiGen.mem_fixSet] at hω
    push Not at hω
    obtain ⟨g, hg, hgω⟩ := hω
    have h2 : 2 ≤ (orbit (((B ⊓ J).subgroupOf J).map φ) ω).ncard := by
      have hsub : ({ω, g ω} : Set (Fin n)) ⊆ orbit (((B ⊓ J).subgroupOf J).map φ) ω := by
        intro x hx
        rcases hx with rfl | hx
        · exact mem_orbit_self x
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact mem_orbit ω (⟨g, hg⟩ : ((B ⊓ J).subgroupOf J).map φ)
      have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_pair (Ne.symm hgω)] at h3
    rw [← Nat.card_coe_set_eq] at h2 ⊢
    rw [hs] at h2 hle ⊢
    rcases s with _ | _ | s
    · simp at h2
    · simpa using hp3
    · exfalso
      have h5 : p ^ 2 ≤ p ^ (s + 1 + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have h6 : p < p ^ 2 := by nlinarith
      omega
  refine le_antisymm ?_ (iSup_le fun U => iSup_le fun _ => iSup_le fun _ => inf_le_left)
  set Γ : Subgroup X := ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
    J ⊓ Subgroup.normalizer (U : Set X) with hΓ
  have hAlt : alternatingGroup (Fin n) ≤ (Γ.subgroupOf J).map φ := by
    refine alternatingGroup_le_of_pairs hRcomm horb3 hω₀ fun ω ω' hω => ?_
    set V := pairStab (((B ⊓ J).subgroupOf J).map φ) ω ω' with hV
    set W : Subgroup ↥J := V.comap φ ⊓ (B ⊓ J).subgroupOf J with hW
    have hWmap : W.map φ = V := by
      refine le_antisymm (fun x hx => ?_) (fun v hv => ?_)
      · obtain ⟨w, hw, rfl⟩ := hx
        exact (Subgroup.mem_inf.1 hw).1
      · obtain ⟨t, ht, htv⟩ := pairStab_le _ ω ω' hv
        refine ⟨t, Subgroup.mem_inf.2 ⟨?_, ht⟩, htv⟩
        rw [Subgroup.mem_comap, htv]
        exact hv
    have hWcard : Nat.card (W.map J.subtype) = Nat.card V := by
      rw [Subgroup.card_map_of_injective J.subtype_injective, ← hWmap,
        Subgroup.card_map_of_injective hφ]
    have hWB : W.map J.subtype ≤ B ⊓ J := by
      rintro _ ⟨w, hw, rfl⟩
      exact (Subgroup.mem_inf.1 hw).2
    set C := B ⊓ Subgroup.centralizer (J : Set X) with hC
    have hWC : W.map J.subtype ≤ Subgroup.normalizer (C : Set X) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact elem_comm hB (Subgroup.mem_inf.1 hy).1 (Subgroup.mem_inf.1 (hWB hx)).1
    have hWCbot : W.map J.subtype ⊓ C = ⊥ := by
      refine le_bot_iff.1 ?_
      rw [← hint]
      exact inf_le_inf_right _ hWB
    have hUcard : Nat.card ↥(W.map J.subtype ⊔ C) = Nat.card V * Nat.card C := by
      have h := card_sup_mul_card_inf hWC
      rwa [hWCbot, Subgroup.card_bot, mul_one, hWcard] at h
    have hUB : W.map J.subtype ⊔ C ≤ B := sup_le (hWB.trans inf_le_left) inf_le_left
    have hUel : IsElemAbelian p (W.map J.subtype ⊔ C) := CFSG.Open.IsElemAbelian.mono hB hUB
    have hU2 : 2 ≤ CFSG.Open.pRank p (W.map J.subtype ⊔ C) := by
      have hVel : IsElemAbelian p V := CFSG.Open.IsElemAbelian.mono hRel (pairStab_le _ ω ω')
      have hCel : IsElemAbelian p C := CFSG.Open.IsElemAbelian.mono hB inf_le_left
      have h1 := card_le_pairStab hRcomm horb ω ω'
      rw [← hV, hRcard, card_eq_pow_pRank hp hVel, ← pow_add] at h1
      have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
      rw [card_eq_pow_pRank hp hUel, card_eq_pow_pRank hp hVel, card_eq_pow_pRank hp hCel,
        ← pow_add] at hUcard
      have h3 := Nat.pow_right_injective hp.two_le hUcard
      omega
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := (GL83.mem_altOn.1 hσ).1
    refine ⟨e.symm ⟨σ, hσA⟩, ?_, by simp [φ]⟩
    show ((e.symm ⟨σ, hσA⟩ : ↥J) : X) ∈ Γ
    have hle : J ⊓ Subgroup.normalizer ((W.map J.subtype ⊔ C : Subgroup X) : Set X) ≤ Γ :=
      le_iSup_of_le (W.map J.subtype ⊔ C) (le_iSup_of_le hUB (le_iSup_of_le hU2 le_rfl))
    refine hle (Subgroup.mem_inf.2 ⟨(e.symm ⟨σ, hσA⟩).2, ?_⟩)
    refine (Subgroup.centralizer_le_normalizer _) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hUle : W.map J.subtype ⊔ C ≤
        Subgroup.centralizer ({((e.symm ⟨σ, hσA⟩ : ↥J) : X)} : Set X) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hφw : φ w ∈ V := (Subgroup.mem_inf.1 hw).1
        have hdisj : Perm.Disjoint (φ w) σ := by
          intro y
          by_cases hy : y ∈ GL83.PiGen.fixSet V
          · exact Or.inl (hy (φ w) hφw)
          · exact Or.inr ((GL83.mem_altOn.1 hσ).2 y hy)
        have hc : φ w * σ = σ * φ w := hdisj.commute.eq
        have hσe : φ (e.symm ⟨σ, hσA⟩) = σ := by simp [φ]
        have hc' : φ (e.symm ⟨σ, hσA⟩ * w) = φ (w * e.symm ⟨σ, hσA⟩) := by
          rw [map_mul, map_mul, hσe, hc]
        have := congrArg (fun z : ↥J => (z : X)) (hφ hc')
        simpa using this.symm
      · intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hc).2) _
          (e.symm ⟨σ, hσA⟩).2).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hUle hu))
  intro x hx
  have hmem : φ ⟨x, hx⟩ ∈ alternatingGroup (Fin n) := (e ⟨x, hx⟩).2
  obtain ⟨y, hy, hyx⟩ := hAlt hmem
  have : y = ⟨x, hx⟩ := hφ hyx
  rw [this] at hy
  exact hy

end Alt

@[expose] def InputI2319Chev2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (J B : Subgroup X),
    ((∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥J ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ :
        Subgroup (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
      (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J ∧ HasFixedPointFreeOrder ε n p)) →
    IsElemAbelian p B → B ≤ Subgroup.normalizer (J : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ J → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    J = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
      J ⊓ Subgroup.normalizer (U : Set X)

theorem card_GL_one_one : Nat.card (GL (Fin 1 ⊕ Fin 1) (ZMod 2)) = 6 := by
  let e : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) (ZMod 2) ≃* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finSumFinEquiv).toMulEquiv
  rw [Nat.card_congr (Units.mapEquiv e).toEquiv, Matrix.card_GL_field 2, ZMod.card]
  decide

theorem card_GL_zero_zero : Nat.card (GL (Fin 0 ⊕ Fin 0) (ZMod 2)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩, ⟨1⟩⟩

theorem inputI27102_of_inputs (h2319 : InputI2319Chev2) : Lemma138.InputI27102 := by
  intro X _ _ p hp hp2 J B hJt hB hBN hsplit hint hrk hB4
  have hcard := card_le_of_split hp hB hsplit hint hrk
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp9 : 9 ≤ p ^ 2 := by nlinarith
  rcases hJt with ⟨k, -, hA⟩ | ⟨k, hA⟩ | ⟨n, ⟨e⟩⟩ | ⟨ε, n, hn, hΩ, hfp⟩
  · exact eq_gamma_of_isAltType hp hp2 hA hB hsplit hint hrk hB4
  · exact eq_gamma_of_isAltType hp hp2 hA hB hsplit hint hrk hB4
  · by_cases hn : 2 ≤ n
    · exact h2319 X p hp hp2 J B (Or.inl ⟨n, hn, ⟨e⟩⟩) hB hBN hcard hB4
    · apply eq_gamma_of_two_le_pRank
      have hle : Nat.card J ≤ Nat.card (GL (Fin n ⊕ Fin n) (ZMod 2)) := by
        rw [Nat.card_congr e.toEquiv]
        exact Subgroup.card_le_card_group _
      have h6 : Nat.card (GL (Fin n ⊕ Fin n) (ZMod 2)) ≤ 6 := by
        interval_cases n
        · rw [card_GL_zero_zero]; omega
        · rw [card_GL_one_one]
      have h1 := pRank_le_one_of_card_lt hp (H := J) (by omega)
      have h2 := pRank_split hp hB hsplit hint
      omega
  · exact h2319 X p hp hp2 J B (Or.inr ⟨ε, n, hn, hΩ, hfp⟩) hB hBN hcard hB4

section TwoSix

variable {G : Type} [Group G] [Finite G]

theorem isComponentOf_top_subgroupOf {L R : Subgroup G} (h : IsComponentOf L R) :
    IsComponentOf (L.subgroupOf R) ⊤ := by
  refine ⟨le_top, ?_, CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe h.1) h.2.2⟩
  have h1 := h.2.1.comap R.subtype
  rwa [show R.comap R.subtype = ⊤ from Subgroup.subgroupOf_self R] at h1

theorem le_centralizer_of_components {Y C C' : Subgroup G} (hC : IsComponentOf C Y)
    (hC' : IsComponentOf C' Y) (hne : C ≠ C') : C ≤ Subgroup.centralizer (C' : Set G) := by
  have hne' : C.subgroupOf Y ≠ C'.subgroupOf Y := by
    intro h
    apply hne
    have := congrArg (Subgroup.map Y.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hC.1, Subgroup.map_subgroupOf_eq_of_le hC'.1] at this
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne (C.subgroupOf Y)
    (C'.subgroupOf Y) (isComponentOf_top_subgroupOf hC) (isComponentOf_top_subgroupOf hC') hne'
  have hmap := congrArg (Subgroup.map Y.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hC.1,
    Subgroup.map_subgroupOf_eq_of_le hC'.1, Subgroup.map_bot] at hmap
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hmap

theorem le_or_le_centralizer {Y C M : Subgroup G} (hC : IsComponentOf C Y) (hMY : M ≤ Y)
    (hYM : Y ≤ Subgroup.normalizer (M : Set G)) :
    C ≤ M ∨ C ≤ Subgroup.centralizer (M : Set G) := by
  haveI : (M.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hMY).2 hYM
  rcases CFSG.ComponentClassification.LocalComponents.normal_contains_or_commutes
      (C.subgroupOf Y) (M.subgroupOf Y) (isComponentOf_top_subgroupOf hC) with h | h
  · left
    have := Subgroup.map_mono (f := Y.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hC.1, Subgroup.map_subgroupOf_eq_of_le hMY] at this
  · right
    have hmap := congrArg (Subgroup.map Y.subtype) h
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hC.1,
      Subgroup.map_subgroupOf_eq_of_le hMY, Subgroup.map_bot] at hmap
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hmap

theorem isComponentOf_gLBConj_of_mem {Y C : Subgroup G} (hC : IsComponentOf C Y) {g : G}
    (hg : g ∈ Subgroup.normalizer (Y : Set G)) : IsComponentOf (GLBConj g C) Y := by
  have hY : GLBConj g Y = Y := gLBConj_eq_of_mem_normalizer hg
  refine ⟨(gLBConj_mono g hC.1).trans hY.le, ?_, ?_⟩
  · have h := isSubnormal_map' (MulAut.conj g⁻¹).toMonoidHom hC.2.1
    rw [← hY]
    exact h
  · exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (C.equivMapOfInjective _ (MulAut.conj g⁻¹).injective).symm hC.2.2

theorem gLBConj_eq_of_mem_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (H : Set G)) : GLBConj g H = H := by
  have hc : ∀ x ∈ H, x * g = g * x := fun x hx => Subgroup.mem_centralizer_iff.1 hg x hx
  ext x
  rw [mem_gLBConj]
  constructor
  · intro hx
    have h1 := hc _ hx
    have e : x = g * x * g⁻¹ := by
      calc x = g⁻¹ * ((g * x * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [h1]
        _ = g * x * g⁻¹ := by group
    rw [e]
    exact hx
  · intro hx
    have h1 := hc x hx
    have e : g * x * g⁻¹ = x := by rw [← h1]; group
    rw [e]
    exact hx

theorem gLBConj_iSup_mem (g : G) (S : Set (Subgroup G)) :
    GLBConj g (⨆ C ∈ S, C) = ⨆ C ∈ S, GLBConj g C := by
  unfold GLBConj
  simp only [Subgroup.map_iSup]

theorem gLBConj_iSup_conj_le {Y J : Subgroup G} {q : G}
    (hqY : q ∈ Subgroup.normalizer (Y : Set G)) (hqJ : GLBConj q J = J) :
    GLBConj q (⨆ g ∈ Y, GLBConj g J) ≤ ⨆ g ∈ Y, GLBConj g J := by
  have h : GLBConj q (⨆ g ∈ Y, GLBConj g J) = ⨆ g ∈ Y, GLBConj q (GLBConj g J) := by
    unfold GLBConj
    simp only [Subgroup.map_iSup]
  rw [h]
  refine iSup₂_le fun g hg => ?_
  have hg' : q⁻¹ * g * q ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hqY) g).1 hg
    simpa using this
  have e : GLBConj q (GLBConj g J) = GLBConj (q⁻¹ * g * q) J := by
    conv_rhs => rw [← hqJ]
    rw [gLBConj_gLBConj, gLBConj_gLBConj]
    congr 1
    group
  rw [e]
  exact le_iSup₂_of_le (q⁻¹ * g * q) hg' le_rfl

theorem le_normalizer_iSup {Y : Subgroup G} (hYL : GLALayer Y = Y) {S : Set (Subgroup G)}
    (hS : ∀ C ∈ S, IsComponentOf C Y) :
    Y ≤ Subgroup.normalizer ((⨆ C ∈ S, C : Subgroup G) : Set G) := by
  have h : GLALayer Y ≤ Subgroup.normalizer ((⨆ C ∈ S, C : Subgroup G) : Set G) := by
    refine sSup_le fun K hK => ?_
    by_cases hKS : K ∈ S
    · exact (le_iSup₂_of_le K hKS le_rfl : K ≤ ⨆ C ∈ S, C).trans Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      refine Subgroup.le_centralizer_iff.2 (iSup₂_le fun C hC => ?_)
      exact le_centralizer_of_components (hS C hC) hK (fun h => hKS (h ▸ hC))
  rwa [hYL] at h

theorem le_sup_compl {Y : Subgroup G} (hYL : GLALayer Y = Y) (S : Set (Subgroup G)) :
    Y ≤ (⨆ C ∈ S, C) ⊔ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S}, C := by
  have h : GLALayer Y ≤
      (⨆ C ∈ S, C) ⊔ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S}, C := by
    refine sSup_le fun K hK => ?_
    by_cases hKS : K ∈ S
    · exact le_sup_of_le_left (le_iSup₂_of_le K hKS le_rfl)
    · exact le_sup_of_le_right
        (le_iSup₂_of_le K (show K ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S} from ⟨hK, hKS⟩)
          le_rfl)
  rwa [hYL] at h

theorem iSup_le_centralizer_compl {Y : Subgroup G} {S : Set (Subgroup G)}
    (hS : ∀ C ∈ S, IsComponentOf C Y) :
    (⨆ C ∈ S, C) ≤ Subgroup.centralizer
      ((⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S}, C : Subgroup G) : Set G) := by
  refine Subgroup.le_centralizer_iff.2 (iSup₂_le fun C' hC' => ?_)
  refine Subgroup.le_centralizer_iff.2 (iSup₂_le fun C hC => ?_)
  exact le_centralizer_of_components (hS C hC) hC'.1 (fun h => hC'.2 (h ▸ hC))

theorem conj_commutatorElement (q x y : G) :
    q * ⁅x, y⁆ * q⁻¹ = ⁅q * x * q⁻¹, q * y * q⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mul_right {a₁ a₂ z₁ z₂ : G} (h1 : z₁ * a₂ = a₂ * z₁)
    (h2 : z₂ * a₁ = a₁ * z₂) (h3 : z₁ * z₂ = z₂ * z₁) :
    ⁅a₁ * z₁, a₂ * z₂⁆ = ⁅a₁, a₂⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h2' : z₂ * a₁⁻¹ = a₁⁻¹ * z₂ := by
    calc z₂ * a₁⁻¹ = a₁⁻¹ * (a₁ * z₂) * a₁⁻¹ := by group
      _ = a₁⁻¹ * (z₂ * a₁) * a₁⁻¹ := by rw [h2]
      _ = a₁⁻¹ * z₂ := by group
  calc a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹
      = a₁ * (z₁ * a₂) * z₂ * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * (a₂ * z₁) * z₂ * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by rw [h1]
    _ = a₁ * a₂ * (z₁ * z₂) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * a₂ * (z₂ * z₁) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by rw [h3]
    _ = a₁ * a₂ * (z₂ * a₁⁻¹) * z₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * a₂ * (a₁⁻¹ * z₂) * z₂⁻¹ * a₂⁻¹ := by rw [h2']
    _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by group

theorem commutatorElement_mul_mul {A A'' : Subgroup G}
    (hAA : A ≤ Subgroup.centralizer (A'' : Set G)) {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A)
    (hb₁ : b₁ ∈ A'') (hb₂ : b₂ ∈ A'') : ⁅a₁ * b₁, a₂ * b₂⁆ = ⁅a₁, a₂⁆ * ⁅b₁, b₂⁆ := by
  have hc : ∀ a ∈ A, ∀ b ∈ A'', a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.1 (hAA ha)) b hb).symm
  rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
  have e1 := hc a₂ ha₂ b₁ hb₁
  have e2 := hc a₁⁻¹ (A.inv_mem ha₁) (b₁ * b₂ * b₁⁻¹)
    (A''.mul_mem (A''.mul_mem hb₁ hb₂) (A''.inv_mem hb₁))
  have e3 := hc a₂⁻¹ (A.inv_mem ha₂) (b₁ * b₂ * b₁⁻¹ * b₂⁻¹)
    (A''.mul_mem (A''.mul_mem (A''.mul_mem hb₁ hb₂) (A''.inv_mem hb₁)) (A''.inv_mem hb₂))
  calc a₁ * b₁ * (a₂ * b₂) * (a₁ * b₁)⁻¹ * (a₂ * b₂)⁻¹
      = a₁ * (b₁ * a₂) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * (a₂ * b₁) * b₂ * b₁⁻¹ * a₁⁻¹ * b₂⁻¹ * a₂⁻¹ := by rw [e1]
    _ = a₁ * a₂ * ((b₁ * b₂ * b₁⁻¹) * a₁⁻¹) * b₂⁻¹ * a₂⁻¹ := by group
    _ = a₁ * a₂ * (a₁⁻¹ * (b₁ * b₂ * b₁⁻¹)) * b₂⁻¹ * a₂⁻¹ := by rw [e2]
    _ = a₁ * a₂ * a₁⁻¹ * ((b₁ * b₂ * b₁⁻¹ * b₂⁻¹) * a₂⁻¹) := by group
    _ = a₁ * a₂ * a₁⁻¹ * (a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹)) := by rw [e3]
    _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by group

theorem le_or_le_of_invariant {p : ℕ} (hp : p.Prime) {Y Qa J : Subgroup G}
    (hYL : GLALayer Y = Y) (hQN : Qa ≤ Subgroup.normalizer (Y : Set G))
    (hJ : GLAPComponent p (Y ⊓ Subgroup.centralizer (Qa : Set G)) J)
    {S' : Set (Subgroup G)} (hS' : ∀ C ∈ S', IsComponentOf C Y)
    (hinv : ∀ g ∈ Qa, ∀ C ∈ S', GLBConj g C ∈ S') :
    J ≤ ⨆ C ∈ S', C ∨ J ≤ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C := by
  have hAA := iSup_le_centralizer_compl hS'
  have hc : ∀ a ∈ ⨆ C ∈ S', C,
      ∀ b ∈ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C, a * b = b * a :=
    fun a ha b hb => ((Subgroup.mem_centralizer_iff.1 (hAA ha)) b hb).symm
  have hYAA := le_sup_compl hYL S'
  have hAY : (⨆ C ∈ S', C) ≤ Y := iSup₂_le fun C hC => (hS' C hC).1
  have hA''Y : (⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C) ≤ Y :=
    iSup₂_le fun C hC => hC.1.1
  have hTinv : ∀ g ∈ Qa, ∀ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'},
      GLBConj g C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'} := by
    intro g hg C hC
    refine ⟨isComponentOf_gLBConj_of_mem hC.1 (hQN hg), fun h => hC.2 ?_⟩
    have h2 := hinv g⁻¹ (Qa.inv_mem hg) _ h
    rwa [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at h2
  have hconj : ∀ (S'' : Set (Subgroup G)), (∀ g ∈ Qa, ∀ C ∈ S'', GLBConj g C ∈ S'') →
      ∀ g ∈ Qa, ∀ a ∈ ⨆ C ∈ S'', C, g * a * g⁻¹ ∈ ⨆ C ∈ S'', C := by
    intro S'' hS'' g hg a ha
    have hle : GLBConj g⁻¹ (⨆ C ∈ S'', C) ≤ ⨆ C ∈ S'', C := by
      rw [gLBConj_iSup_mem]
      exact iSup₂_le fun C hC =>
        le_iSup₂_of_le (GLBConj g⁻¹ C) (hS'' g⁻¹ (Qa.inv_mem hg) C hC) le_rfl
    apply hle
    rw [mem_gLBConj]
    have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
    rw [e]
    exact ha
  have hJC : J ≤ Subgroup.centralizer (Qa : Set G) := hJ.1.trans inf_le_right
  have hJY : J ≤ Y := hJ.1.trans inf_le_left
  have hdec : ∀ a ∈ ⨆ C ∈ S', C,
      ∀ b ∈ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C, a * b ∈ J → ∀ q ∈ Qa,
      ∃ z ∈ (⨆ C ∈ S', C) ⊓ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C,
        q * a * q⁻¹ = a * z ∧ q * b * q⁻¹ = b * z⁻¹ := by
    intro a ha b hb hj q hq
    have hqj : q * (a * b) * q⁻¹ = a * b := by
      have h1 := (Subgroup.mem_centralizer_iff.1 (hJC hj)) q hq
      calc q * (a * b) * q⁻¹ = (a * b) * q * q⁻¹ := by rw [h1]
        _ = a * b := by group
    have hxA := hconj S' hinv q hq a ha
    have hyA := hconj _ hTinv q hq b hb
    have hxy : (q * a * q⁻¹) * (q * b * q⁻¹) = a * b := by
      rw [← hqj]
      group
    have hz : a⁻¹ * (q * a * q⁻¹) = b * (q * b * q⁻¹)⁻¹ := by
      calc a⁻¹ * (q * a * q⁻¹) = a⁻¹ * ((q * a * q⁻¹) * (q * b * q⁻¹)) * (q * b * q⁻¹)⁻¹ := by
            group
        _ = a⁻¹ * (a * b) * (q * b * q⁻¹)⁻¹ := by rw [hxy]
        _ = b * (q * b * q⁻¹)⁻¹ := by group
    have hzA : a⁻¹ * (q * a * q⁻¹) ∈ ⨆ C ∈ S', C :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hxA
    have hzA'' : a⁻¹ * (q * a * q⁻¹) ∈
        ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C := by
      rw [hz]
      exact Subgroup.mul_mem _ hb (Subgroup.inv_mem _ hyA)
    refine ⟨a⁻¹ * (q * a * q⁻¹), Subgroup.mem_inf.2 ⟨hzA, hzA''⟩, by group, ?_⟩
    have hzb := hc _ (Subgroup.inv_mem _ hzA) b hb
    calc q * b * q⁻¹ = (b * (q * b * q⁻¹)⁻¹)⁻¹ * b := by group
      _ = (a⁻¹ * (q * a * q⁻¹))⁻¹ * b := by rw [hz]
      _ = b * (a⁻¹ * (q * a * q⁻¹))⁻¹ := hzb
  have hJH : J ≤ ((⨆ C ∈ S', C) ⊓ Subgroup.centralizer (Qa : Set G)) ⊔
      ((⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C) ⊓
        Subgroup.centralizer (Qa : Set G)) := by
    calc J = ⁅J, J⁆ := (glaPComponent_perfect hJ).symm
      _ ≤ _ := by
        refine Subgroup.commutator_le.2 fun j₁ hj₁ j₂ hj₂ => ?_
        obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := exists_mul_of_mem_sup hAA (hYAA (hJY hj₁))
        obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := exists_mul_of_mem_sup hAA (hYAA (hJY hj₂))
        rw [commutatorElement_mul_mul hAA ha₁ ha₂ hb₁ hb₂]
        refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
          (Subgroup.mem_sup_right (Subgroup.mem_inf.2 ⟨?_, ?_⟩))
        · rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha₁ ha₂)
            (Subgroup.inv_mem _ ha₁)) (Subgroup.inv_mem _ ha₂)
        · rw [Subgroup.mem_centralizer_iff]
          intro q hq
          obtain ⟨z₁, hz₁, hqa₁, -⟩ := hdec a₁ ha₁ b₁ hb₁ hj₁ q hq
          obtain ⟨z₂, hz₂, hqa₂, -⟩ := hdec a₂ ha₂ b₂ hb₂ hj₂ q hq
          have key : q * ⁅a₁, a₂⁆ * q⁻¹ = ⁅a₁, a₂⁆ := by
            rw [conj_commutatorElement, hqa₁, hqa₂]
            exact commutatorElement_mul_right (hc a₂ ha₂ z₁ hz₁.2).symm
              (hc a₁ ha₁ z₂ hz₂.2).symm (hc z₂ hz₂.1 z₁ hz₁.2).symm
          calc q * ⁅a₁, a₂⁆ = q * ⁅a₁, a₂⁆ * q⁻¹ * q := by group
            _ = ⁅a₁, a₂⁆ * q := by rw [key]
        · rw [commutatorElement_def]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hb₁ hb₂)
            (Subgroup.inv_mem _ hb₁)) (Subgroup.inv_mem _ hb₂)
        · rw [Subgroup.mem_centralizer_iff]
          intro q hq
          obtain ⟨z₁, hz₁, -, hqb₁⟩ := hdec a₁ ha₁ b₁ hb₁ hj₁ q hq
          obtain ⟨z₂, hz₂, -, hqb₂⟩ := hdec a₂ ha₂ b₂ hb₂ hj₂ q hq
          have key : q * ⁅b₁, b₂⁆ * q⁻¹ = ⁅b₁, b₂⁆ := by
            rw [conj_commutatorElement, hqb₁, hqb₂]
            exact commutatorElement_mul_right (hc z₁⁻¹ (Subgroup.inv_mem _ hz₁.1) b₂ hb₂)
              (hc z₂⁻¹ (Subgroup.inv_mem _ hz₂.1) b₁ hb₁)
              (hc z₁⁻¹ (Subgroup.inv_mem _ hz₁.1) z₂⁻¹ (Subgroup.inv_mem _ hz₂.2))
          calc q * ⁅b₁, b₂⁆ = q * ⁅b₁, b₂⁆ * q⁻¹ * q := by group
            _ = ⁅b₁, b₂⁆ * q := by rw [key]
  set H₁ : Subgroup G := (⨆ C ∈ S', C) ⊓ Subgroup.centralizer (Qa : Set G) with hH₁
  set H₂ : Subgroup G := (⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C) ⊓
    Subgroup.centralizer (Qa : Set G) with hH₂
  have hH'Y : H₁ ⊔ H₂ ≤ Y ⊓ Subgroup.centralizer (Qa : Set G) :=
    sup_le (inf_le_inf_right _ hAY) (inf_le_inf_right _ hA''Y)
  have hJ' : GLAPComponent p (H₁ ⊔ H₂) J :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_down hp hJ hJH hH'Y
  have hH₁₂ : H₁ ≤ Subgroup.centralizer (H₂ : Set G) :=
    (inf_le_left.trans hAA).trans (Subgroup.centralizer_le inf_le_left)
  have hN₁ : (H₁.subgroupOf (H₁ ⊔ H₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer
        ((Subgroup.le_centralizer_iff.1 hH₁₂).trans (Subgroup.centralizer_le_normalizer _)))
  have hN₂ : (H₂.subgroupOf (H₁ ⊔ H₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (sup_le (hH₁₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer)
  rcases CFSG.HardMathSupport.Solomon.Coordinator.i183_le_or_commutator_eq_bot hp hJ'
      (le_sup_left : H₁ ≤ H₁ ⊔ H₂) (hN := hN₁) with h1 | h1
  · exact Or.inl (h1.trans inf_le_left)
  rcases CFSG.HardMathSupport.Solomon.Coordinator.i183_le_or_commutator_eq_bot hp hJ'
      (le_sup_right : H₂ ≤ H₁ ⊔ H₂) (hN := hN₂) with h2 | h2
  · exact Or.inr (h2.trans inf_le_left)
  exfalso
  have hc1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
  have hc2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  have htop : barX p (H₁ ⊔ H₂) (H₁ ⊔ H₂) = barX p (H₁ ⊔ H₂) H₁ ⊔ barX p (H₁ ⊔ H₂) H₂ :=
    Lemma137.barX_sup_of_le le_sup_left le_sup_right
  rw [barX_self] at htop
  have hJtop : barX p (H₁ ⊔ H₂) J ≤
      Subgroup.centralizer (((⊤ : Subgroup (↥(H₁ ⊔ H₂) ⧸ GLAPPrimeCore p ↥(H₁ ⊔ H₂)))) : Set _) := by
    rw [htop]
    exact Subgroup.le_centralizer_iff.2
      (sup_le (Subgroup.le_centralizer_iff.1 hc1) (Subgroup.le_centralizer_iff.1 hc2))
  have hcomm : ⁅barX p (H₁ ⊔ H₂) J, barX p (H₁ ⊔ H₂) J⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2
      (hJtop.trans (Subgroup.centralizer_le (fun x _ => Subgroup.mem_top x)))
  rw [barX_perfect_of_glaPComponent hJ'] at hcomm
  have hnt : Nontrivial ↥(barX p (H₁ ⊔ H₂) J) :=
    CFSG.ComponentClassification.Quasisimple.nontrivial hJ'.2.2.1.2.2
  exact (Subgroup.nontrivial_iff_ne_bot _).1 hnt hcomm

theorem inputI226_holds : Lemma138.InputI226 := by
  intro G _ _ p hp Y Qa _ hYL _ hQN J hJ0
  have hLH : GLAPLayer p (Y ⊓ Subgroup.centralizer (Qa : Set G)) ≤
      Y ⊓ Subgroup.centralizer (Qa : Set G) := Lemma138.glaPLayer_le_self p _
  have hLN : Y ⊓ Subgroup.centralizer (Qa : Set G) ≤
      Subgroup.normalizer (GLAPLayer p (Y ⊓ Subgroup.centralizer (Qa : Set G)) : Set G) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer p
      Subgroup.le_normalizer
  have hLsn : IsSubnormal (GLAPLayer p (Y ⊓ Subgroup.centralizer (Qa : Set G)))
      (Y ⊓ Subgroup.centralizer (Qa : Set G)) :=
    IsSubnormal.step hLH ((Subgroup.normal_subgroupOf_iff_le_normalizer hLH).2 hLN)
      (IsSubnormal.refl _)
  have hJ : GLAPComponent p (Y ⊓ Subgroup.centralizer (Qa : Set G)) J :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPComponent_up hp hJ0 hLH
      (isSubnormal_trans' hJ0.2.1 hLsn)
  have hJY : J ≤ Y := hJ.1.trans inf_le_left
  have hJC : J ≤ Subgroup.centralizer (Qa : Set G) := hJ.1.trans inf_le_right
  have hQJ : ∀ q ∈ Qa, GLBConj q J = J := fun q hq =>
    gLBConj_eq_of_mem_centralizer ((Subgroup.le_centralizer_iff.1 hJC) hq)
  have hJN : J ≤ ⨆ g ∈ Y, GLBConj g J := by
    have h1 := le_iSup₂ (f := fun g (_ : g ∈ Y) => GLBConj g J) (1 : G) Y.one_mem
    rwa [gLBConj_one] at h1
  have hNY : (⨆ g ∈ Y, GLBConj g J) ≤ Y := iSup₂_le fun g hg =>
    (gLBConj_mono g hJY).trans (gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hg)).le
  have hYN : Y ≤ Subgroup.normalizer ((⨆ g ∈ Y, GLBConj g J : Subgroup G) : Set G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => Lemma138.mem_iSup_conj hy hx
    · intro hx
      have h1 := Lemma138.mem_iSup_conj (Y.inv_mem hy) hx
      have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [e] at h1
  have hNinv : ∀ q ∈ Qa, GLBConj q (⨆ g ∈ Y, GLBConj g J) ≤ ⨆ g ∈ Y, GLBConj g J :=
    fun q hq => gLBConj_iSup_conj_le (hQN hq) (hQJ q hq)
  have hSc : ∀ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ≤ ⨆ g ∈ Y, GLBConj g J},
      IsComponentOf C Y := fun C hC => hC.1
  have hSN : (⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ≤ ⨆ g ∈ Y, GLBConj g J}, C) ≤
      ⨆ g ∈ Y, GLBConj g J := iSup₂_le fun C hC => hC.2
  have hNS : (⨆ g ∈ Y, GLBConj g J) ≤
      ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ≤ ⨆ g ∈ Y, GLBConj g J}, C := by
    have hSY := le_normalizer_iSup hYL hSc
    have hJS : J ≤ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ≤ ⨆ g ∈ Y, GLBConj g J}, C := by
      refine le_of_perfect_le_sup_centralizer (iSup_le_centralizer_compl hSc) ?_
        (glaPComponent_perfect hJ) (hJY.trans (le_sup_compl hYL _))
      refine Subgroup.le_centralizer_iff.2 (iSup₂_le fun C hC => ?_)
      rcases le_or_le_centralizer hC.1 hNY hYN with h | h
      · exact absurd ⟨hC.1, h⟩ hC.2
      · exact h.trans (Subgroup.centralizer_le hJN)
    exact iSup₂_le fun g hg =>
      (gLBConj_mono g hJS).trans (gLBConj_eq_of_mem_normalizer (hSY hg)).le
  refine ⟨{C : Subgroup G | IsComponentOf C Y ∧ C ≤ ⨆ g ∈ Y, GLBConj g J}, hSc,
    fun g hg C hC => ⟨isComponentOf_gLBConj_of_mem hC.1 (hQN hg),
      (gLBConj_mono g hC.2).trans (hNinv g hg)⟩, le_antisymm hNS hSN, ?_⟩
  intro S' hS'S hinv hne
  have hS'c : ∀ C ∈ S', IsComponentOf C Y := fun C hC => (hS'S hC).1
  have hS'le : (⨆ C ∈ S', C) ≤
      ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ≤ ⨆ g ∈ Y, GLBConj g J}, C :=
    iSup₂_le fun C hC => le_iSup₂_of_le C (hS'S hC) le_rfl
  rcases le_or_le_of_invariant hp hYL hQN hJ hS'c hinv with hJA | hJA
  · refine le_antisymm hS'le (hSN.trans (iSup₂_le fun g hg => ?_))
    exact (gLBConj_mono g hJA).trans
      (gLBConj_eq_of_mem_normalizer (le_normalizer_iSup hYL hS'c hg)).le
  · exfalso
    obtain ⟨C, hC⟩ := hne
    have hTY := le_normalizer_iSup hYL
      (S := {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}) (fun C hC => hC.1)
    have hNT : (⨆ g ∈ Y, GLBConj g J) ≤ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C :=
      iSup₂_le fun g hg => (gLBConj_mono g hJA).trans (gLBConj_eq_of_mem_normalizer (hTY hg)).le
    have hC1 : C ≤ ⨆ C ∈ S', C := le_iSup₂_of_le C hC le_rfl
    have hC2 : C ≤ ⨆ C ∈ {C : Subgroup G | IsComponentOf C Y ∧ C ∉ S'}, C :=
      (hS'S hC).2.trans hNT
    have hCC : C ≤ Subgroup.centralizer (C : Set G) :=
      (hC1.trans (iSup_le_centralizer_compl hS'c)).trans (Subgroup.centralizer_le hC2)
    have hbot : C = ⊥ := by
      rw [← Subgroup.isPerfect_iff.1 ⟨(hS'c C hC).2.2.1⟩]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 hCC
    have hnt : Nontrivial ↥C := CFSG.ComponentClassification.Quasisimple.nontrivial (hS'c C hC).2.2
    exact (Subgroup.nontrivial_iff_ne_bot C).1 hnt hbot

end TwoSix

@[expose] def InputI2711 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime → p ≠ 2 → ∀ (L B : Subgroup X),
    CFSG.IsKGroup ↥L → CFSG.Open.IsQuasisimple ↥L → IsElemAbelian p B →
    B ≤ Subgroup.normalizer (L : Set X) →
    (∀ A : Subgroup X, A ≤ B ⊔ L → IsElemAbelian p A → Nat.card A ≤ Nat.card B) →
    4 ≤ CFSG.Open.pRank p B →
    ∀ J0 : Subgroup X,
      IsComponentOf J0 (⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)) →
      ((∃ k : ℕ, 5 ≤ k * p ∧ IsAltType (k * p) J0) ∨ (∃ k : ℕ, IsAltType (k * p + 2) J0) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ HasFixedPointFreeOrder ε n p ∧
          Nonempty (↥J0 ≃* ↥(⁅(StatedSp n (ZMod 2)), (StatedSp n (ZMod 2))⁆ : Subgroup
            (GL (Fin n ⊕ Fin n) (ZMod 2))))) ∨
        (∃ (ε : Bool) (n : ℕ), 1 ≤ n ∧ IsOmegaTwo ε (n + 1) J0 ∧
          HasFixedPointFreeOrder ε n p)) →
      ¬ (p = 3 ∧ IsAltType 5 J0) →
      (∃ E : Subgroup X, E ≤ B ∧ Nat.card B ≤ p ^ 2 * Nat.card E ∧
        GLAPLayer p (J0 ⊓ Subgroup.centralizer (E : Set X)) ≠ ⊥) →
      L = ⨆ (U : Subgroup X) (_ : U ≤ B) (_ : 2 ≤ CFSG.Open.pRank p U),
        L ⊓ Subgroup.normalizer (U : Set X)

theorem inputI2711_iff_inputI27111 : InputI2711 ↔ Lemma138.InputI27111 :=
  ⟨fun h => h, fun h => h⟩

theorem inputI2711_of_inputI27111 (h : Lemma138.InputI27111) : InputI2711 :=
  inputI2711_iff_inputI27111.2 h

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims138
