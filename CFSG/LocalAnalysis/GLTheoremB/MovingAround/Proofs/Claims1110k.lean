module

import CFSG.HardMathSupport.Solomon.Coordinator.I10_21D4Two
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21D4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110i2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110k

open CFSG.Open Subgroup
open CFSG.HardMathSupport.Solomon.Coordinator
  (i1021_caseA i1020_pi_elemAbelian i1020_exists_mulSingle_mem i1020_commutator_top i1021_exists_prime_ne)
open scoped commutatorElement

section PowRank

variable {F : Type} [Group F]

theorem exists_factor_cover_of_not_le_ker [IsSimpleGroup F] (hnc : ∃ a b : F, a * b ≠ b * a) {q : ℕ}
    (hq : q.Prime) (hcov : ∀ (X1 : Type) [Group X1] [Finite X1] (ψ : X1 →* F), Function.Surjective ψ →
      commutator X1 = ⊤ → ψ.ker ≤ center X1 → IsPGroup q ψ.ker → Function.Injective ψ)
    {X : Type} [Group X] [Finite X] {r : ℕ} (φ : X →* (Fin r → F)) (hφ : Function.Surjective φ)
    (hYq : IsPGroup q φ.ker) (hC : ¬ centralizer (φ.ker : Set X) ≤ φ.ker) :
    ∃ i : Fin r, ∃ L : Subgroup X, (∀ l ∈ L, φ l i = 1 → l = 1) ∧ (∀ a : F, ∃ l ∈ L, φ l i = a) ∧
      ∀ l ∈ L, ∀ h : X, φ h i = 1 → l * h = h * l := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  set Y : Subgroup X := φ.ker with hYdef
  set C : Subgroup X := centralizer (Y : Set X) with hCdef
  have hCn : (C.map φ).Normal := Subgroup.normal_centralizer.map φ hφ
  have hCne : C.map φ ≠ ⊥ := fun h => hC ((Subgroup.map_eq_bot_iff _).1 h)
  obtain ⟨i, hi⟩ := i1020_exists_mulSingle_mem hnc hCn hCne
  set ψ : X →* F := (Pi.evalMonoidHom (fun _ : Fin r => F) i).comp φ with hψdef
  let good : Subgroup X → Prop := fun M =>
    M ≤ C ∧ (∀ m ∈ M, ∀ j, j ≠ i → φ m j = 1) ∧ M.map ψ = ⊤
  have hgood0 : good (C ⊓ (Subgroup.pi {j | j ≠ i} fun _ => (⊥ : Subgroup F)).comap φ) := by
    refine ⟨inf_le_left, fun m hm j hj => ?_, ?_⟩
    · have := (mem_pi _).1 (mem_comap.1 (mem_inf.1 hm).2) j hj
      rwa [mem_bot] at this
    · rw [eq_top_iff]
      intro a _
      obtain ⟨c, hc, hca⟩ := mem_map.1 (hi a)
      refine ⟨c, mem_inf.2 ⟨hc, mem_comap.2 ((mem_pi _).2 fun j hj => ?_)⟩, ?_⟩
      · rw [hca, Pi.mulSingle_eq_of_ne hj, mem_bot]
      · simp [hψdef, hca]
  have hex : ∃ n, ∃ M, good M ∧ Nat.card M = n := ⟨_, _, hgood0, rfl⟩
  obtain ⟨L, hL, hLc⟩ := Nat.find_spec hex
  have hLmin : ∀ M, good M → Nat.card L ≤ Nat.card M := fun M hM =>
    hLc ▸ Nat.find_min' hex ⟨M, hM, rfl⟩
  obtain ⟨hLC, hLi, hLψ⟩ := hL
  have hLperf : ⁅L, L⁆ = L := by
    have hle : ⁅L, L⁆ ≤ L := commutator_le_self L
    refine eq_of_le_of_card_ge hle (hLmin _ ⟨hle.trans hLC, fun m hm => hLi m (hle hm), ?_⟩)
    rw [map_commutator, hLψ, i1020_commutator_top hnc]
  have hcomm : ∀ l ∈ L, ∀ h : X, φ h i = 1 → l * h = h * l := by
    intro x hxL h hh
    have hLH : ⁅L, ψ.ker⁆ ≤ Y := by
      rw [commutator_le]
      intro l hl g hg
      rw [hYdef, MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
      funext j
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
      by_cases hj : j = i
      · subst hj
        have : φ g j = 1 := hg
        simp [this]
      · simp [hLi l hl j hj]
    have hYL : ⁅Y, L⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hLC)
    have h1 : ⁅⁅L, ψ.ker⁆, L⁆ = ⊥ := le_bot_iff.1 (hYL ▸ commutator_mono hLH le_rfl)
    have h2 : ⁅⁅ψ.ker, L⁆, L⁆ = ⊥ := by rw [commutator_comm ψ.ker L]; exact h1
    have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
    rw [hLperf] at h3
    have h4 : ⁅x, h⁆ ∈ ⁅L, ψ.ker⁆ := commutator_mem_commutator hxL (by simpa [hψdef] using hh)
    rw [h3, mem_bot] at h4
    exact commutatorElement_eq_one_iff_mul_comm.1 h4
  set ψL : ↥L →* F := ψ.comp L.subtype with hψLdef
  have hψL : Function.Surjective ψL := by
    intro a
    have ha : a ∈ L.map ψ := hLψ ▸ mem_top a
    obtain ⟨l, hl, hla⟩ := mem_map.1 ha
    exact ⟨⟨l, hl⟩, hla⟩
  have hperfL : commutator ↥L = ⊤ := (Subgroup.isPerfect_iff.2 hLperf).commutator_eq_top
  have hkerY : ∀ l : ↥L, ψL l = 1 → (l : X) ∈ Y := by
    intro l hl
    rw [hYdef, MonoidHom.mem_ker]
    funext j
    by_cases hj : j = i
    · subst hj
      exact hl
    · exact hLi l l.2 j hj
  have hkerC : ψL.ker ≤ center ↥L := by
    intro l hl
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.1 (hLC g.2)) (l : X) (hkerY l hl)).symm
  have hkerq : IsPGroup q ψL.ker := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have hgY : ((g : ↥L) : X) ∈ φ.ker := hkerY g g.2
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hYq ⟨_, hgY⟩
    refine ⟨k, ?_⟩
    have e1 : orderOf g = orderOf (g : ↥L) := (Subgroup.orderOf_coe g).symm
    have e2 : orderOf (g : ↥L) = orderOf ((g : ↥L) : X) := (Subgroup.orderOf_coe _).symm
    have e3 : orderOf (⟨((g : ↥L) : X), hgY⟩ : φ.ker) = orderOf ((g : ↥L) : X) :=
      Subgroup.orderOf_mk _ _
    exact e1.trans (e2.trans (e3.symm.trans hk))
  have hinj := hcov ↥L ψL hψL hperfL hkerC hkerq
  refine ⟨i, L, fun l hl h1 => ?_, fun a => ?_, hcomm⟩
  · have h2 : ψL ⟨l, hl⟩ = ψL 1 := by
      rw [map_one]
      exact h1
    exact congrArg Subtype.val (hinj h2)
  · obtain ⟨⟨l, hl⟩, hla⟩ := hψL a
    exact ⟨l, hl, hla⟩

theorem mul_le_pRank_of_surjective_pi [Finite F] [IsSimpleGroup F] (hnc : ∃ a b : F, a * b ≠ b * a)
    {q n : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hn : 0 < n) {V : Subgroup F} (hV : IsElemAbelian 2 V)
    (hVc : Nat.card V = 2 ^ n) (hqF : n ≤ CFSG.Open.pRank q (⊤ : Subgroup F))
    (hcov : ∀ (X1 : Type) [Group X1] [Finite X1] (ψ : X1 →* F), Function.Surjective ψ →
      commutator X1 = ⊤ → ψ.ker ≤ center X1 → IsPGroup q ψ.ker → Function.Injective ψ) :
    ∀ (m : ℕ) (X : Type) [Group X] [Finite X], Nat.card X ≤ m → ∀ (r : ℕ) (φ : X →* (Fin r → F)),
      Function.Surjective φ → r * n ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := by
  have : Fact q.Prime := ⟨hq⟩
  intro m
  induction m with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ m ih =>
    intro X _ _ hX r φ hφ
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · subst hr0
      simp
    by_cases hYq : IsPGroup q φ.ker
    · by_cases hC : centralizer (φ.ker : Set X) ≤ φ.ker
      ·
        have hYne : φ.ker ≠ ⊥ := by
          intro hbot
          obtain ⟨a, ha⟩ := exists_ne (1 : F)
          obtain ⟨x, hx⟩ := hφ (Pi.mulSingle ⟨0, hr0⟩ a)
          have hx1 : x ∈ φ.ker := hC (by
            rw [hbot, mem_centralizer_iff]
            intro h hh
            rw [SetLike.mem_coe, mem_bot] at hh
            rw [hh, one_mul, mul_one])
          rw [MonoidHom.mem_ker, hx] at hx1
          exact ha (by simpa using congrFun hx1 ⟨0, hr0⟩)
        obtain ⟨hT, hTc⟩ := i1020_pi_elemAbelian hV hVc r
        have h := i1021_caseA hq hq2 (Nat.mul_pos hn hr0) hT hTc φ hφ hYq hYne hC
        rwa [Nat.mul_comm] at h
      ·
        obtain ⟨i, L, hLinj, hLsurj, hLcomm⟩ := exists_factor_cover_of_not_le_ker hnc hq hcov φ hφ hYq hC
        obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
        set H : Subgroup X := ((Pi.evalMonoidHom (fun _ : Fin (r' + 1) => F) i).comp φ).ker
          with hHdef
        have hmemH : ∀ h : X, h ∈ H ↔ φ h i = 1 := fun h => by simp [hHdef]
        set φ' : H →* (Fin r' → F) :=
          (MonoidHom.pi fun j => Pi.evalMonoidHom (fun _ : Fin (r' + 1) => F) (i.succAbove j)).comp
            (φ.comp H.subtype) with hφ'def
        have hφ' : Function.Surjective φ' := by
          intro g
          obtain ⟨y, hy⟩ := hφ (i.insertNth 1 g)
          have hyH : y ∈ H := by rw [hmemH, hy, Fin.insertNth_apply_same]
          refine ⟨⟨y, hyH⟩, ?_⟩
          funext j
          simp [hφ'def, hy, Fin.insertNth_apply_succAbove]
        obtain ⟨a, ha⟩ := exists_ne (1 : F)
        obtain ⟨x, -, hxa⟩ := hLsurj a
        have hxH : x ∉ H := fun h => ha (hxa ▸ (hmemH x).1 h)
        have hHlt : Nat.card H < Nat.card X := by
          rw [← card_top (G := X)]
          refine card_lt_of_lt (lt_top_iff_ne_top.2 fun h => hxH ?_)
          rw [h]
          exact mem_top x
        have ihH := ih H (by omega) r' φ' hφ'
        set ψL : ↥L →* F := ((Pi.evalMonoidHom (fun _ : Fin (r' + 1) => F) i).comp φ).comp L.subtype
          with hψLdef
        have hbij : Function.Bijective ψL := by
          refine ⟨fun l₁ l₂ h12 => ?_, fun b => ?_⟩
          · have h1 : φ (((l₁ : X)) * (l₂ : X)⁻¹) i = 1 := by
              have e1 : φ (l₁ : X) i = φ (l₂ : X) i := h12
              simp [e1]
            have h2 := hLinj _ (L.mul_mem l₁.2 (L.inv_mem l₂.2)) h1
            exact Subtype.ext (mul_inv_eq_one.1 h2)
          · obtain ⟨l, hl, hlb⟩ := hLsurj b
            exact ⟨⟨l, hl⟩, hlb⟩
        have hLrank : n ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥L) := by
          rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt (MulEquiv.ofBijective ψL hbij)]
          exact hqF
        obtain ⟨E₁, -, hE₁, hE₁c⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup ↥L)
        obtain ⟨E₂, -, hE₂, hE₂c⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup ↥H)
        set A : Subgroup X := E₁.map L.subtype with hAdef
        set B : Subgroup X := E₂.map H.subtype with hBdef
        have hA : IsElemAbelian q A := CFSG.SectionRank.isElemAbelian_map hE₁ _
        have hB : IsElemAbelian q B := CFSG.SectionRank.isElemAbelian_map hE₂ _
        have hAc : Nat.card A = q ^ CFSG.Open.pRank q (⊤ : Subgroup ↥L) := by
          rw [hAdef, card_map_of_injective L.subtype_injective, hE₁c]
        have hBc : Nat.card B = q ^ CFSG.Open.pRank q (⊤ : Subgroup ↥H) := by
          rw [hBdef, card_map_of_injective H.subtype_injective, hE₂c]
        have hAL : A ≤ L := map_subtype_le _
        have hBH : B ≤ H := map_subtype_le _
        have hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
          hLcomm a (hAL ha) b ((hmemH b).1 (hBH hb))
        have hinf : A ⊓ B = ⊥ := by
          rw [eq_bot_iff]
          intro z hz
          exact (mem_bot).2 (hLinj z (hAL hz.1) ((hmemH z).1 (hBH hz.2)))
        have hcard : Nat.card (A ⊔ B : Subgroup X) =
            q ^ (CFSG.Open.pRank q (⊤ : Subgroup ↥L) + CFSG.Open.pRank q (⊤ : Subgroup ↥H)) := by
          have h := Claims1110e.card_sup_mul_card_inf_of_commute' A B hcAB
          rw [hinf, card_bot, mul_one, hAc, hBc, ← pow_add] at h
          exact h
        have hAB : IsElemAbelian q (A ⊔ B) := IsElemAbelian.sup_of_commute hA hB hcAB
        have hle := CFSG.SectionRank.le_pRank hq.one_lt le_top hAB hcard
        calc (r' + 1) * n = n + r' * n := by ring
          _ ≤ CFSG.Open.pRank q (⊤ : Subgroup ↥L) + CFSG.Open.pRank q (⊤ : Subgroup ↥H) := Nat.add_le_add hLrank ihH
          _ ≤ CFSG.Open.pRank q (⊤ : Subgroup X) := hle
    ·
      obtain ⟨p, hp, hpq, hpY⟩ := i1021_exists_prime_ne hYq
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p φ.ker))
      set P' : Subgroup X := (P : Subgroup φ.ker).map φ.ker.subtype with hP'def
      have hfr : normalizer (P' : Set X) ⊔ φ.ker = ⊤ := Sylow.normalizer_sup_eq_top P
      have hP'Y : P' ≤ φ.ker := map_subtype_le _
      obtain ⟨m', hm⟩ := IsPGroup.iff_card.1 (P.isPGroup'.map φ.ker.subtype)
      have hP'q : ¬ q ∣ Nat.card P' := by
        rw [hm]
        intro h
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm
      by_cases htop : normalizer (P' : Set X) = ⊤
      ·
        have hP'n : P'.Normal := normalizer_eq_top_iff.1 htop
        have hP'ne : P' ≠ ⊥ :=
          (map_eq_bot_iff_of_injective _ φ.ker.subtype_injective).not.2
            (P.ne_bot_of_dvd_card hpY)
        have hlt : Nat.card (X ⧸ P') < Nat.card X := by
          rw [card_eq_card_quotient_mul_card_subgroup P']
          have h1 : 1 < Nat.card P' := (one_lt_card_iff_ne_bot P').2 hP'ne
          have h2 : 0 < Nat.card (X ⧸ P') := Nat.card_pos
          nlinarith
        have hsurj : Function.Surjective (QuotientGroup.lift P' φ hP'Y) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          exact ⟨x, rfl⟩
        have := ih (X ⧸ P') (by omega) r (QuotientGroup.lift P' φ hP'Y) hsurj
        rwa [CFSG.SectionRank.pRank_quotient_eq P' hP'q] at this
      ·
        set X₀ : Subgroup X := normalizer (P' : Set X)
        have hφ₀ : Function.Surjective (φ.comp X₀.subtype) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          have hx : x ∈ X₀ ⊔ φ.ker := hfr ▸ mem_top x
          obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.1 hx
          refine ⟨⟨a, ha⟩, ?_⟩
          simp [MonoidHom.mem_ker.1 hb]
        have hlt : Nat.card X₀ < Nat.card X := by
          rw [← card_top (G := X)]
          exact card_lt_of_lt (lt_top_iff_ne_top.2 htop)
        have := ih X₀ (by omega) r (φ.comp X₀.subtype) hφ₀
        exact this.trans (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt X₀.subtype
          X₀.subtype_injective)

end PowRank

section Components

variable {G : Type} [Group G] [Finite G]

open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut barAut_mk)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns (mem_gLAPPrimeCoreOf_iff inf_gLAPPrimeCoreOf_eq)

theorem mk_eq_of_conj_ne_pComponent {Y L L' : Subgroup G} (hL : GLAPComponent 5 Y L)
    (hL' : GLAPComponent 5 Y L') (hne : L ≠ L') {x : G} (hx : x ∈ L') (a b : ↥Y)
    (hab : (a : G) = x⁻¹ * b * x) (hb : (b : G) ∈ L) :
    QuotientGroup.mk' (GLAPPrimeCore 5 ↥Y) a = QuotientGroup.mk' (GLAPPrimeCore 5 ↥Y) b := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hc := Claims1110i.comm_mem_core_of_ne_pComponent hL' hL hne.symm (L'.inv_mem hx) (L.inv_mem hb)
  obtain ⟨hmem, hcore⟩ := (mem_gLAPPrimeCoreOf_iff 5 Y _).1 hc
  convert hcore using 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hab]
  group

theorem le_normalizer_of_ne_pComponent {Y L L' : Subgroup G} (hL : GLAPComponent 5 Y L)
    (hL' : GLAPComponent 5 Y L') (hne : L ≠ L') : L' ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_gLBConj_eq]
  have hxY : x ∈ Y := hL'.1 hx
  have hLx : GLAPComponent 5 Y (GLBConj x L) := by
    have h1 := glaPComponent_gLBConj hL x
    rwa [gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hxY)] at h1
  refine glaPComponent_unique hLx hL ?_
  unfold barX
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : x * (w : G) * x⁻¹ ∈ L := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hw)
    refine ⟨⟨x * (w : G) * x⁻¹, hL.1 hw'⟩, Subgroup.mem_subgroupOf.2 hw', ?_⟩
    exact (mk_eq_of_conj_ne_pComponent hL hL' hne hx w ⟨_, hL.1 hw'⟩ (by group) hw').symm
  · rintro _ ⟨l, hl, rfl⟩
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    have hmem : x⁻¹ * (l : G) * x ∈ GLBConj x L := mem_gLBConj.2 (by group; exact hl')
    refine ⟨⟨x⁻¹ * (l : G) * x, Y.mul_mem (Y.mul_mem (Y.inv_mem hxY) l.2) hxY⟩,
      Subgroup.mem_subgroupOf.2 hmem, ?_⟩
    exact mk_eq_of_conj_ne_pComponent hL hL' hne hx _ l rfl hl'

theorem comm_mem_primeCoreOf_of_ne {Y L L' : Subgroup G} (hL : GLAPComponent 5 Y L)
    (hL' : GLAPComponent 5 Y L') (hne : L ≠ L') {x l : G} (hx : x ∈ L') (hl : l ∈ L) :
    x * l * x⁻¹ * l⁻¹ ∈ GLAPPrimeCoreOf 5 L := by
  have h1 := Claims1110i.comm_mem_core_of_ne_pComponent hL' hL hne.symm hx hl
  have hxN := le_normalizer_of_ne_pComponent hL hL' hne hx
  have h2 : x * l * x⁻¹ * l⁻¹ ∈ L := L.mul_mem ((Subgroup.mem_normalizer_iff.1 hxN l).1 hl) (L.inv_mem hl)
  rw [← inf_gLAPPrimeCoreOf_eq (by norm_num : Nat.Prime 5) hL.2.1]
  exact ⟨h2, h1⟩

theorem exists_factor_hom {Y : Subgroup G} {𝒞 : Set (Subgroup G)}
    (h𝒞 : ∀ L ∈ 𝒞, Claims1110i.IsD4Comp Y L) {L : Subgroup G} (hL : L ∈ 𝒞) :
    ∃ Φ : ↥(⨆ L' ∈ 𝒞, L') →* ↥CFSG.EvenSmallLie.OmegaEight.omegaT,
      (∀ a, ∃ (l : G) (hl : l ∈ ⨆ L' ∈ 𝒞, L'), l ∈ L ∧ Φ ⟨l, hl⟩ = a) ∧
      ∀ L' ∈ 𝒞, L' ≠ L → ∀ (x : G) (hx : x ∈ ⨆ L' ∈ 𝒞, L'), x ∈ L' → Φ ⟨x, hx⟩ = 1 := by
  set J : Subgroup G := ⨆ L' ∈ 𝒞, L' with hJdef
  have hLJ : ∀ L' ∈ 𝒞, L' ≤ J := fun L' hL' => le_iSup₂_of_le L' hL' le_rfl
  have hJN : J ≤ Subgroup.normalizer (L : Set G) := by
    refine iSup₂_le fun L' hL' => ?_
    by_cases h : L' = L
    · subst h
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_ne_pComponent (h𝒞 L hL).1 (h𝒞 L' hL').1 (Ne.symm h)
  set γ : ↥J →* MulAut (barOf 5 L) := (barAut 5 L).comp (Subgroup.inclusion hJN) with hγdef
  have hγL : ∀ (l : G) (hl : l ∈ L),
      γ ⟨l, hLJ L hL hl⟩ = MulAut.conj (QuotientGroup.mk ⟨l, hl⟩ : barOf 5 L) := by
    intro l hl
    ext t
    induction t using QuotientGroup.induction_on with
    | H y =>
      rw [hγdef, MonoidHom.comp_apply, barAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
  have hγL' : ∀ (L' : Subgroup G) (hL' : L' ∈ 𝒞), L' ≠ L → ∀ (x : G) (hx : x ∈ L'),
      γ ⟨x, hLJ L' hL' hx⟩ = 1 := by
    intro L' hL' hne x hx
    ext t
    induction t using QuotientGroup.induction_on with
    | H y =>
      rw [hγdef, MonoidHom.comp_apply, barAut_mk, MulAut.one_apply, QuotientGroup.eq]
      have hc := comm_mem_primeCoreOf_of_ne (h𝒞 L hL).1 (h𝒞 L' hL').1 (Ne.symm hne) hx (L.inv_mem y.2)
      obtain ⟨hmem, hcore⟩ := (mem_gLAPPrimeCoreOf_iff 5 L _).1 hc
      convert hcore using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.normalizerMonoidHom_apply_apply_coe,
        Subgroup.coe_inclusion, inv_inv]
      group
  set ι : barOf 5 L →* MulAut (barOf 5 L) := MulAut.conj with hιdef
  have hrange : ∀ g : ↥J, γ g ∈ ι.range := by
    have hle : J ≤ (ι.range.comap γ).map J.subtype := by
      refine iSup₂_le fun L' hL' x hx => ⟨⟨x, hLJ L' hL' hx⟩, ?_, rfl⟩
      refine Subgroup.mem_comap.2 ?_
      by_cases h : L' = L
      · subst h
        rw [hγL x hx]
        exact ⟨_, rfl⟩
      · rw [hγL' L' hL' h x hx]
        exact one_mem _
    intro g
    obtain ⟨g', hg', hgg'⟩ := hle g.2
    have : g' = g := Subtype.ext hgg'
    rw [← this]
    exact hg'
  have hker : ι.ker = Subgroup.center (barOf 5 L) := by
    ext z
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro h g
      have h1 := congrArg (fun f : MulAut (barOf 5 L) => f g) h
      simp only [hιdef, MulAut.conj_apply, MulAut.one_apply] at h1
      exact eq_mul_inv_iff_mul_eq.1 h1.symm
    · intro h
      ext g
      simp only [hιdef, MulAut.conj_apply, MulAut.one_apply]
      rw [← h g, mul_inv_cancel_right]
  set Θ : ↥ι.range ≃* barOf 5 L ⧸ Subgroup.center (barOf 5 L) :=
    (QuotientGroup.quotientKerEquivRange ι).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)
  have hcl : StatedClassicalModel (barOf 5 L ⧸ Subgroup.center (barOf 5 L)) .POmegaPlus 4 2 1 := by
    rcases (h𝒞 L hL).2.2 with h | ⟨h4, -⟩
    · exact h
    · norm_num at h4
  obtain ⟨e⟩ := CFSG.EvenSmallLie.OmegaEight.nonempty_mulEquiv_omegaT (Or.inl ⟨by decide, hcl⟩)
  set Φ : ↥J →* ↥CFSG.EvenSmallLie.OmegaEight.omegaT :=
    e.toMonoidHom.comp (Θ.toMonoidHom.comp (γ.codRestrict ι.range hrange)) with hΦdef
  refine ⟨Φ, fun a => ?_, fun L' hL' hne x hx hxL' => ?_⟩
  · obtain ⟨s, hs⟩ := (Θ.symm (e.symm a)).2
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective s
    refine ⟨l, hLJ L hL hl, hl, ?_⟩
    have h1 : γ.codRestrict ι.range hrange ⟨l, hLJ L hL hl⟩ = Θ.symm (e.symm a) := by
      apply Subtype.ext
      show γ ⟨l, hLJ L hL hl⟩ = ((Θ.symm (e.symm a) : ↥ι.range) : MulAut (barOf 5 L))
      rw [hγL l hl]
      exact hs
    simp only [hΦdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, MulEquiv.apply_symm_apply]
  · have h1 : γ.codRestrict ι.range hrange ⟨x, hx⟩ = 1 := Subtype.ext (hγL' L' hL' hne x hxL')
    simp only [hΦdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1, map_one]

theorem inputD4ThreeRank_holds :
    Claims1110i.InputD4ThreeRank := by
  intro G _ _ Y _ 𝒞 h𝒞
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J : Subgroup G := ⨆ L ∈ 𝒞, L with hJdef
  have hΦ : ∀ L : ↥𝒞, ∃ Φ : ↥J →* ↥CFSG.EvenSmallLie.OmegaEight.omegaT,
      (∀ a, ∃ (l : G) (hl : l ∈ J), l ∈ (L : Subgroup G) ∧ Φ ⟨l, hl⟩ = a) ∧
      ∀ L' ∈ 𝒞, L' ≠ (L : Subgroup G) → ∀ (x : G) (hx : x ∈ J), x ∈ L' → Φ ⟨x, hx⟩ = 1 :=
    fun L => exists_factor_hom h𝒞 L.2
  choose Φ hΦs hΦt using hΦ
  set r : ℕ := Nat.card ↥𝒞 with hr
  set e : Fin r ≃ ↥𝒞 := (Finite.equivFin ↥𝒞).symm with hedef
  set φ : ↥J →* (Fin r → ↥CFSG.EvenSmallLie.OmegaEight.omegaT) := MonoidHom.pi fun j => Φ (e j)
    with hφdef
  have hsingle : ∀ j a, Pi.mulSingle j a ∈ φ.range := by
    intro j a
    obtain ⟨l, hlJ, hlL, hla⟩ := hΦs (e j) a
    refine ⟨⟨l, hlJ⟩, ?_⟩
    funext k
    by_cases hk : k = j
    · subst hk
      simp [hφdef, hla]
    · have hne : ((e j : ↥𝒞) : Subgroup G) ≠ (e k : Subgroup G) := fun h =>
        hk (e.injective (Subtype.ext h.symm))
      rw [Pi.mulSingle_eq_of_ne hk]
      exact hΦt (e k) (e j) (e j).2 hne l hlJ hlL
  have hφ : Function.Surjective φ := by
    intro f
    have hf : f ∈ φ.range := by
      rw [← Finset.noncommProd_mulSingle f]
      exact Subgroup.noncommProd_mem _ _ fun j _ => hsingle j (f j)
    exact MonoidHom.mem_range.1 hf
  have hS : StatedClassicalModel ↥CFSG.EvenSmallLie.OmegaEight.omegaT .POmegaPlus 4 2 1 :=
    CFSG.EvenSmallLie.OmegaEight.statedClassicalModel_omegaT
  obtain ⟨-, hsimple⟩ :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus _ 4 2 1 hS
  haveI := hsimple
  have hLie : CFSG.Models.LieModel ↥CFSG.EvenSmallLie.OmegaEight.omegaT .POmegaPlus 4 2 1 :=
    ⟨hS.1, Or.inl hS⟩
  obtain ⟨hperfF, ⟨eH⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_four_two_row hLie
  have hnc : ∃ a b : ↥CFSG.EvenSmallLie.OmegaEight.omegaT, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have : commutator ↥CFSG.EvenSmallLie.OmegaEight.omegaT = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a _
      rw [Subgroup.mem_centralizer_iff]
      intro b _
      exact (hc a b).symm
    rw [hperfF] at this
    exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup ↥CFSG.EvenSmallLie.OmegaEight.omegaT)).1
      inferInstance this
  obtain ⟨V, hV, hVc⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i1021_d4_two_rank_four hS
  have hqF := CFSG.HardMathSupport.Solomon.Coordinator.i1021_d4_pRank_ge_four hS
  have hcov : ∀ (X1 : Type) [Group X1] [Finite X1] (ψ : X1 →* ↥CFSG.EvenSmallLie.OmegaEight.omegaT),
      Function.Surjective ψ → commutator X1 = ⊤ → ψ.ker ≤ center X1 → IsPGroup 3 ψ.ker →
        Function.Injective ψ := by
    intro X1 _ _ ψ hψ hperf hker hp
    have : Finite (CFSG.Blueprint.Multiplier.generic .POmegaPlus 4 2 1 ×
        CFSG.Blueprint.Multiplier.exceptional .POmegaPlus 4 2 1) :=
      Nat.finite_of_card_ne_zero
        (by rw [CFSG.HardMathSupport.Solomon.Coordinator.i1021_card_table_D4]; norm_num)
    have hdvd := CFSG.HardMathSupport.Solomon.Coordinator.i1021_card_ker_dvd ψ hψ hker hperf eH
    rw [CFSG.HardMathSupport.Solomon.Coordinator.i1021_card_table_D4] at hdvd
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hp
    have hk0 : k = 0 := by
      rw [hk] at hdvd
      by_contra hne
      have h3 : 3 ∣ 4 := (dvd_pow_self 3 hne).trans hdvd
      omega
    have hbot : ψ.ker = ⊥ := by
      rw [hk0] at hk
      exact Subgroup.card_eq_one.1 (by simpa using hk)
    exact (MonoidHom.ker_eq_bot_iff ψ).1 hbot
  have h := mul_le_pRank_of_surjective_pi hnc Nat.prime_three (by norm_num) (by norm_num : 0 < 4) hV
    hVc hqF hcov _ ↥J le_rfl r φ hφ
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) ≤ CFSG.Open.pRank 3 J := by
    have := CFSG.SectionRank.pRank_le_map (by norm_num : 1 < 3) J.subtype J.subtype_injective ⊤
    rwa [Subgroup.map_top, Subgroup.range_subtype] at this
  have hnc𝒞 : 𝒞.ncard = r := (Nat.card_coe_set_eq 𝒞).symm
  rw [hnc𝒞]
  omega

end Components

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110k
