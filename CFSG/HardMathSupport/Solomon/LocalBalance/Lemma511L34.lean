module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510ii
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

set_option linter.unusedSectionVars false

namespace Lemma511L34Ns

@[expose] def InputL34AutInner : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeFour Y →
    ∀ (E S : Subgroup (MulAut Y)) (x : Y), IsElemAbelian 3 E → Nat.card E = 9 →
      E ≤ innerAut Y → x ≠ 1 → MulAut.conj x ∈ E → Nat.Coprime 3 (Nat.card S) →
      E ≤ Subgroup.normalizer (S : Set (MulAut Y)) →
      ∀ s ∈ S, ∀ c : Y, c * x = x * c → s c = c

@[expose] def InputL34AutOuter : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLThreeFour Y →
    ∀ (E E' S : Subgroup (MulAut Y)) (x : Y), E ≤ E' → IsElemAbelian 3 E' → Nat.card E = 9 →
      x ≠ 1 → MulAut.conj x ∈ E' → Nat.Coprime 3 (Nat.card S) →
      (∀ e ∈ E, ∀ s ∈ S, s * e = e * s) →
      ∀ s ∈ S, ∀ c : Y, c * x = x * c → s c = c

section Elem

variable {G : Type} [Group G] [Finite G]

theorem barAut_eq_conj' {L : Subgroup G} {z : G} (hn : z ∈ Subgroup.normalizer (L : Set G))
    (hz : z ∈ L) :
    barAut 3 L ⟨z, hn⟩ = MulAut.conj (QuotientGroup.mk (⟨z, hz⟩ : ↥L) : barOf 3 L) := by
  ext w
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [barAut_mk]
    show (QuotientGroup.mk (L.normalizerMonoidHom ⟨z, hn⟩ x) : barOf 3 L) = _
    rw [MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl

theorem eq_one_of_mem_core' {L : Subgroup G} {z : G} (hz : z ∈ L) (hz3 : z ^ 3 = 1)
    (hcore : (⟨z, hz⟩ : ↥L) ∈ GLAPPrimeCore 3 ↥L) : z = 1 := by
  let w : ↥(GLAPPrimeCore 3 ↥L) := ⟨⟨z, hz⟩, hcore⟩
  have hw3 : w ^ 3 = 1 := Subtype.ext (Subtype.ext hz3)
  have hd1 : orderOf w ∣ Nat.card (GLAPPrimeCore 3 ↥L) := orderOf_dvd_natCard w
  have hd2 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  have hcop := coprime_card_gLAPPrimeCore_aux 3 ↥L
  have h3 : orderOf w = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1
  have h4 : w = 1 := orderOf_eq_one_iff.1 h3
  have h6 : z = (((w : ↥(GLAPPrimeCore 3 ↥L)) : ↥L) : G) := rfl
  rw [h6, h4]
  rfl

theorem mem_normalizer_of_conj_mem {M : Type*} [Group M] {S : Subgroup M} {g : M}
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) (h' : ∀ x ∈ S, g⁻¹ * x * g⁻¹⁻¹ ∈ S) :
    g ∈ Subgroup.normalizer (S : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  have := h' _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_of_forall_conj_mem {M : Type*} [Group M] {S K : Subgroup M}
    (h : ∀ g ∈ K, ∀ x ∈ S, g * x * g⁻¹ ∈ S) : K ≤ Subgroup.normalizer (S : Set M) :=
  fun g hg => mem_normalizer_of_conj_mem (h g hg) (h g⁻¹ (K.inv_mem hg))

theorem coprime_card_sup_of_normalizes {O S₀ : Subgroup G} (hO : Nat.Coprime 3 (Nat.card O))
    (hS : Nat.Coprime 3 (Nat.card S₀)) (hn : S₀ ≤ Subgroup.normalizer (O : Set G)) :
    Nat.Coprime 3 (Nat.card (O ⊔ S₀ : Subgroup G)) := by
  set T : Subgroup G := O ⊔ S₀ with hT
  have hOT : O ≤ T := le_sup_left
  have hST : S₀ ≤ T := le_sup_right
  have hTN : T ≤ Subgroup.normalizer (O : Set G) := sup_le Subgroup.le_normalizer hn
  have hOn : (O.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOT).2 hTN
  let φ : ↥T →* ↥T ⧸ O.subgroupOf T := QuotientGroup.mk' (O.subgroupOf T)
  have hsup : O.subgroupOf T ⊔ S₀.subgroupOf T = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOT hST, Subgroup.subgroupOf_self]
  have hmap : (S₀.subgroupOf T).map φ = ⊤ := by
    have h1 : (O.subgroupOf T ⊔ S₀.subgroupOf T).map φ = ⊤ := by
      rw [hsup, Subgroup.map_top, MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective _
    rw [Subgroup.map_sup] at h1
    have h2 : (O.subgroupOf T).map φ = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_bot]
      exact (QuotientGroup.eq_one_iff x).2 hx
    rwa [h2, bot_sup_eq] at h1
  have hdvd : Nat.card (↥T ⧸ O.subgroupOf T) ∣ Nat.card S₀ := by
    have h1 := Subgroup.card_map_dvd (S₀.subgroupOf T) φ
    rw [hmap, Subgroup.card_top] at h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hST).toEquiv] at h1
  have hcardO : Nat.card (O.subgroupOf T) = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOT).toEquiv
  have hmul : Nat.card (O.subgroupOf T) * (O.subgroupOf T).index = Nat.card T :=
    Subgroup.card_mul_index _
  rw [← hmul, hcardO]
  exact Nat.Coprime.mul_right hO (Nat.Coprime.coprime_dvd_right hdvd hS)

end Elem

section Witness

variable {G : Type} [Group G] [Finite G]

theorem not_slob_of_witness {L F A S₀ : Subgroup G} {b : G}
    (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (hFL : F ≤ L) (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hS₀ : S₀ ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G))
    (hS₀c : Nat.Coprime 3 (Nat.card S₀))
    (hnot : ¬ ⁅L, S₀⁆ ≤ GLAPPrimeCoreOf 3 L)
    (hAS : A ≤ Subgroup.normalizer (S₀ : Set G))
    (hFS : ∀ f ∈ F, ∀ s ∈ S₀, s * f * s⁻¹ * f⁻¹ ∈ GLAPPrimeCoreOf 3 L) :
    ¬ IsStronglyLocallyOneBalanced 3 (F ⊔ A) b L := by
  intro hslob
  set O : Subgroup G := GLAPPrimeCoreOf 3 L with hO
  have hOL : O ≤ L := Subgroup.map_subtype_le _
  have hS₀O : S₀ ≤ Subgroup.normalizer (O : Set G) := fun s hs =>
    Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf 3 (hS₀ hs).1
  have hSle : (O ⊔ S₀ : Subgroup G) ≤
      Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :=
    sup_le (fun x hx => ⟨Subgroup.le_normalizer (hOL hx), hLb (hOL hx)⟩) hS₀
  have hcop : Nat.Coprime 3 (Nat.card (O ⊔ S₀ : Subgroup G)) :=
    coprime_card_sup_of_normalizes (Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 L) hS₀c hS₀O
  have hconj : ∀ g : G, (∀ x ∈ O, g * x * g⁻¹ ∈ O) → (∀ x ∈ S₀, g * x * g⁻¹ ∈ O ⊔ S₀) →
      ∀ x ∈ (O ⊔ S₀ : Subgroup G), g * x * g⁻¹ ∈ (O ⊔ S₀ : Subgroup G) := by
    intro g hgO hgS
    have hle : (O ⊔ S₀ : Subgroup G) ≤ (O ⊔ S₀ : Subgroup G).comap (MulAut.conj g).toMonoidHom :=
      sup_le (fun x hx => by
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact Subgroup.mem_sup_left (hgO x hx)) (fun x hx => by
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hgS x hx)
    intro x hx
    have := hle hx
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hFnorm : F ≤ Subgroup.normalizer ((O ⊔ S₀ : Subgroup G) : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun f hf => hconj f ?_ ?_
    · intro x hx
      exact (Subgroup.mem_normalizer_iff.1
        (Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf 3 (Subgroup.le_normalizer (hFL hf))) x).1 hx
    · intro s hs
      have h1 : f * s * f⁻¹ * s⁻¹ ∈ O := by
        have := O.inv_mem (hFS f hf s hs)
        simpa [mul_assoc] using this
      have h2 : f * s * f⁻¹ = (f * s * f⁻¹ * s⁻¹) * s := by group
      rw [h2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hs)
  have hAnorm : A ≤ Subgroup.normalizer ((O ⊔ S₀ : Subgroup G) : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun a ha => hconj a ?_ ?_
    · intro x hx
      exact (Subgroup.mem_normalizer_iff.1 (Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf 3 (hAN ha)) x).1 hx
    · intro s hs
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hAS ha) s).1 hs)
  have hnorm : (F ⊔ A) ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((O ⊔ S₀ : Subgroup G) : Set G) :=
    inf_le_left.trans (sup_le hFnorm hAnorm)
  have h := hslob _ hSle hcop hnorm
  exact hnot ((Subgroup.commutator_mono le_rfl le_sup_right).trans h)

end Witness

section Branches

variable {G : Type} [Group G] [Finite G]

theorem mem_gLADelta_iff {p : ℕ} {D : Subgroup G} {x : G} :
    x ∈ GLADelta p D ↔ ∀ d ∈ D, d ≠ 1 → x ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({d} : Set G)) := by
  simp only [GLADelta, Subgroup.mem_iInf]

theorem commutator_mem_core_of_fix {L : Subgroup G} {s f : G}
    (hsN : s ∈ Subgroup.normalizer (L : Set G)) (hf : f ∈ L)
    (h : barAut 3 L ⟨s, hsN⟩ (QuotientGroup.mk (⟨f, hf⟩ : ↥L)) = QuotientGroup.mk ⟨f, hf⟩) :
    s * f * s⁻¹ * f⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
  rw [barAut_mk] at h
  have h1 : (QuotientGroup.mk (L.normalizerMonoidHom ⟨s, hsN⟩ ⟨f, hf⟩ * (⟨f, hf⟩ : ↥L)⁻¹) :
      barOf 3 L) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, h, mul_inv_cancel]
  have h2 := Subgroup.mem_map_of_mem L.subtype ((QuotientGroup.eq_one_iff _).1 h1)
  exact h2

theorem not_slob_of_branch_a (h31 : Lemma31) (h59 : Lemma59) (i34 : InputL34AutInner) {m : ℕ}
    (hS : GLStanding G m 3) (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBZeroMax 3 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hLC : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hΛ : L ≤ lambdaOf 3 B b) (hψ : ¬ L ≤ psiStarGroup 3 B)
    (hL34 : IsLThreeFour (barOf 3 L)) {A F : Subgroup G} (hA : IsEkIn 3 2 B A)
    (hAf : ∀ a ∈ A, InducesFieldAut 3 L a)
    (hFel : IsElemAbelian 3 F) (hFL : F ≤ L) {y : G} (hyF : y ∈ F) (hyB : y ∈ B) (hy1 : y ≠ 1) :
    ¬ IsStronglyLocallyOneBalanced 3 (F ⊔ A) b L := by
  have hBel : IsElemAbelian 3 B := hB.1.1
  have hLb : L ≤ Subgroup.centralizer ({b} : Set G) := hLC.1
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := fun a ha => (hAf a ha).fst
  have hnotB := Lemma53Ns.not_stronglyBalanced_of_le_lambdaOf hLC hΛ
  obtain ⟨S₀, hS₀, hS₀c, hS₀n, hS₀not⟩ : ∃ S : Subgroup G,
      S ≤ Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({b} : Set G) ∧
      Nat.Coprime 3 (Nat.card S) ∧ B ⊓ Subgroup.normalizer (L : Set G) ≤
        Subgroup.normalizer (S : Set G) ∧ ¬ ⁅L, S⁆ ≤ GLAPPrimeCoreOf 3 L := by
    by_contra hcon
    apply hnotB
    intro S h1 h2 h3
    by_contra h4
    exact hcon ⟨S, h1, h2, h3, h4⟩
  obtain ⟨-, -, -, hrel, hinn⟩ :=
    Lemma510iiNs.lemma31iii_of_alternative_a h31 h59 hS hC hB hb hb1 hLC hΛ hψ
  have hE9 : Nat.card (autBar 3 B L) = 9 := Lemma510iiNs.card_autBar_eq_of_relIndex hLC hrel
  have hEinn : autBar 3 B L ≤ innerAut (barOf 3 L) := Lemma510iiNs.autBar_le_innerAut hLC hinn
  have hBel' : IsElemAbelian 3 (B ⊓ Subgroup.normalizer (L : Set G)) :=
    Lemma54Ns.isElemAbelian_of_le' hBel inf_le_left
  have hEel : IsElemAbelian 3 (autBar 3 B L) :=
    isElemAbelian_map (CFSG.HardMathSupport.Solomon.LocalBalance.isElemAbelian_subgroupOf hBel') _
  set St : Subgroup (MulAut (barOf 3 L)) :=
    (S₀.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hSt
  have hStc : Nat.Coprime 3 (Nat.card St) := by
    have h1 := Subgroup.card_map_dvd (S₀.subgroupOf (Subgroup.normalizer (L : Set G)))
      (barAut 3 L)
    have h2 : Nat.card (S₀.subgroupOf (Subgroup.normalizer (L : Set G))) = Nat.card S₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hS₀.trans inf_le_left)).toEquiv
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hS₀c
  have hEnorm : autBar 3 B L ≤ Subgroup.normalizer (St : Set (MulAut (barOf 3 L))) := by
    refine le_normalizer_of_forall_conj_mem ?_
    rintro e ⟨γ, hγ, rfl⟩ _ ⟨τ, hτ, rfl⟩
    have hg : (γ : G) ∈ B ⊓ Subgroup.normalizer (L : Set G) := Subgroup.mem_subgroupOf.1 hγ
    have hτS : (τ : G) ∈ S₀ := Subgroup.mem_subgroupOf.1 hτ
    refine ⟨γ * τ * γ⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 (hS₀n hg) _).1 hτS)
  have hyL : y ∈ L := hFL hyF
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  set x : barOf 3 L := QuotientGroup.mk ⟨y, hyL⟩ with hx
  have hx1 : x ≠ 1 := by
    intro h
    exact hy1 (eq_one_of_mem_core' hyL (hBel.2 y hyB) ((QuotientGroup.eq_one_iff _).1 h))
  have hxE : MulAut.conj x ∈ autBar 3 B L :=
    ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.2 ⟨hyB, hyN⟩, barAut_eq_conj' hyN hyL⟩
  have hfix := i34 (barOf 3 L) hL34 (autBar 3 B L) St x hEel hE9 hEinn hx1 hxE hStc hEnorm
  have hFS : ∀ f ∈ F, ∀ s ∈ S₀, s * f * s⁻¹ * f⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
    intro f hf s hs
    have hfL := hFL hf
    have hsN : s ∈ Subgroup.normalizer (L : Set G) := (hS₀ hs).1
    have hmem : barAut 3 L ⟨s, hsN⟩ ∈ St := ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    have hcomm : (QuotientGroup.mk ⟨f, hfL⟩ : barOf 3 L) * x = x * QuotientGroup.mk ⟨f, hfL⟩ := by
      rw [hx, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (elemAbelian_comm hFel hf hyF)
    exact commutator_mem_core_of_fix hsN hfL (hfix _ hmem _ hcomm)
  exact not_slob_of_witness hLb hFL hAN hS₀ hS₀c hS₀not (fun a ha => hS₀n ⟨hA.1 ha, hAN ha⟩) hFS

theorem not_slob_of_branch_b (h191 : Lemma54Ns.Input19_1_2) (i34 : InputL34AutOuter) {m : ℕ}
    (hS : GLStanding G m 3) {B : Subgroup G} (hBel : IsElemAbelian 3 B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {L : Subgroup G}
    (hLC : GLAPComponent 3 (Subgroup.centralizer ({b} : Set G)) L)
    (hL34 : IsLThreeFour (barOf 3 L)) {D : Subgroup G} (hD : IsEkIn 3 2 B D)
    (hnot : ¬ ⁅L, GLADelta 3 D ⊓ Subgroup.centralizer ({b} : Set G)⁆ ≤ GLAPPrimeCoreOf 3 L)
    {A F : Subgroup G} (hA : IsEkIn 3 2 B A) (hbA : b ∈ A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G))
    (hFel : IsElemAbelian 3 F) (hFL : F ≤ L) {y : G} (hyF : y ∈ F) (hyB : y ∈ B) (hy1 : y ≠ 1) :
    ¬ IsStronglyLocallyOneBalanced 3 (F ⊔ A) b L := by
  have := hS.simple
  obtain ⟨hDB, hDel, hDcard⟩ := hD
  have hLb : L ≤ Subgroup.centralizer ({b} : Set G) := hLC.1
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  set X : Subgroup G := GLADelta 3 D ⊓ C with hXdef
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDcard
    norm_num at hDcard
  have hbD : b ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact elemAbelian_comm hBel (hDB hd) hb
  obtain ⟨hnorm, hmain⟩ :=
    h191 G hS.nonabelian hS.kProper 3 Nat.prime_three D hDel hDne b hbD hb1 (hBel.2 b hb)
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := hnorm L hLC
  have hnot' : ¬ ⁅L, X⁆ ≤ GLAPPrimeCoreOf 3 C := by
    intro hle
    apply hnot
    have hLX : ⁅L, X⁆ ≤ L := Subgroup.commutator_le.2 fun ℓ hℓ x hx => by
      rw [commutatorElement_def]
      have h1 := (Subgroup.mem_normalizer_iff.1 (hXN hx) ℓ⁻¹).1 (L.inv_mem hℓ)
      have h2 := L.mul_mem hℓ h1
      simpa [mul_assoc] using h2
    intro y hy
    have h3 := gLAPPrimeCoreOf_inf_le Nat.prime_three C L ⟨hle hy, hLX hy⟩
    rwa [inf_eq_right.2 hLC.1] at h3
  obtain ⟨hker, hDN, -⟩ := hmain L hLC hnot'
  obtain ⟨d₀, hd₀D, hd₀1⟩ : ∃ d ∈ D, d ≠ 1 := by
    obtain ⟨d, hd⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
    exact ⟨d, d.2, fun h => hd (Subtype.ext h)⟩
  have hXc : Nat.Coprime 3 (Nat.card X) := by
    have hle : X ≤ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d₀} : Set G)) := by
      intro x hx
      exact mem_gLADelta_iff.1 hx.1 d₀ hd₀D hd₀1
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      (Lemma512Ns.card_gLAPPrimeCoreOf_coprime 3 _)
  have hAcomm : ∀ a ∈ A, ∀ z ∈ B, a * z = z * a := fun a ha z hz =>
    elemAbelian_comm hBel (hA.1 ha) hz
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun a ha x hx => ⟨?_, ?_⟩
    · refine mem_gLADelta_iff.2 fun d hd hd1 => ?_
      have had : a ∈ Subgroup.centralizer ({d} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        rw [Set.mem_singleton_iff] at hc
        subst hc
        exact (hAcomm a ha c (hDB hd)).symm
      exact (Subgroup.mem_normalizer_iff.1
        (Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf 3 (Subgroup.le_normalizer had)) x).1
        (mem_gLADelta_iff.1 hx.1 d hd hd1)
    · have hbx : b * x = x * b := (Subgroup.mem_centralizer_iff.1 hx.2) b (Set.mem_singleton b)
      have hab : a * b = b * a := hAcomm a ha b (hA.1 hbA)
      show a * x * a⁻¹ ∈ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      rw [Set.mem_singleton_iff] at hc
      rw [hc]
      calc b * (a * x * a⁻¹) = (b * a) * x * a⁻¹ := by group
        _ = (a * b) * x * a⁻¹ := by rw [← hab]
        _ = a * (b * x) * a⁻¹ := by group
        _ = a * (x * b) * a⁻¹ := by rw [hbx]
        _ = (a * x * a⁻¹) * (a * b * a⁻¹) := by group
        _ = (a * x * a⁻¹) * b := by rw [hab]; group
  have hBel' : IsElemAbelian 3 (B ⊓ Subgroup.normalizer (L : Set G)) :=
    Lemma54Ns.isElemAbelian_of_le' hBel inf_le_left
  have hBtel : IsElemAbelian 3 (autBar 3 B L) :=
    isElemAbelian_map (CFSG.HardMathSupport.Solomon.LocalBalance.isElemAbelian_subgroupOf hBel') _
  set Dt : Subgroup (MulAut (barOf 3 L)) :=
    (D.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hDt
  have hDcard9 : Nat.card Dt = 9 := by
    rw [hDt, Lemma54Ns.card_map_barAut_of_kerB_eq_bot hDN hker, hDcard]
    norm_num
  have hDtB : Dt ≤ autBar 3 B L := Subgroup.map_mono (by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨hDB hx, x.2⟩)
  set St : Subgroup (MulAut (barOf 3 L)) :=
    (X.subgroupOf (Subgroup.normalizer (L : Set G))).map (barAut 3 L) with hSt
  have hStc : Nat.Coprime 3 (Nat.card St) := by
    have h1 := Subgroup.card_map_dvd (X.subgroupOf (Subgroup.normalizer (L : Set G)))
      (barAut 3 L)
    have h2 : Nat.card (X.subgroupOf (Subgroup.normalizer (L : Set G))) = Nat.card X :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN).toEquiv
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hXc
  have hcent : ∀ e ∈ Dt, ∀ s ∈ St, s * e = e * s := by
    rintro _ ⟨⟨d, hdN⟩, hdD, rfl⟩ _ ⟨⟨s, hsN⟩, hsX, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hs : s ∈ X := Subgroup.mem_subgroupOf.1 hsX
    have hdD' : d ∈ D := Subgroup.mem_subgroupOf.1 hdD
    have := Subgroup.mem_centralizer_iff.1 (Lemma54Ns.gLADelta_le_centralizer hdD' hs.1) d
      (Set.mem_singleton d)
    exact this.symm
  have hyL : y ∈ L := hFL hyF
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hyL
  set x : barOf 3 L := QuotientGroup.mk ⟨y, hyL⟩ with hx
  have hx1 : x ≠ 1 := by
    intro h
    exact hy1 (eq_one_of_mem_core' hyL (hBel.2 y hyB) ((QuotientGroup.eq_one_iff _).1 h))
  have hxE : MulAut.conj x ∈ autBar 3 B L :=
    ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.2 ⟨hyB, hyN⟩, barAut_eq_conj' hyN hyL⟩
  have hfix := i34 (barOf 3 L) hL34 Dt (autBar 3 B L) St x hDtB hBtel hDcard9 hx1 hxE hStc hcent
  have hFS : ∀ f ∈ F, ∀ s ∈ X, s * f * s⁻¹ * f⁻¹ ∈ GLAPPrimeCoreOf 3 L := by
    intro f hf s hs
    have hfL := hFL hf
    have hsN : s ∈ Subgroup.normalizer (L : Set G) := hXN hs
    have hmem : barAut 3 L ⟨s, hsN⟩ ∈ St := ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    have hcomm : (QuotientGroup.mk ⟨f, hfL⟩ : barOf 3 L) * x = x * QuotientGroup.mk ⟨f, hfL⟩ := by
      rw [hx, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext (elemAbelian_comm hFel hf hyF)
    exact commutator_mem_core_of_fix hsN hfL (hfix _ hmem _ hcomm)
  exact not_slob_of_witness hLb hFL hAN (fun x hx => ⟨hXN hx, hx.2⟩) hXc
    (fun h => hnot h) hAX hFS

end Branches

theorem gapL34_of_inputs (h31 : Lemma31) (h59 : Lemma59) (h191 : Lemma54Ns.Input19_1_2)
    (i34i : InputL34AutInner) (i34o : InputL34AutOuter) :
    ∀ (G : Type) [Group G] [Finite G] (m : ℕ), GLStanding G m 3 → GLCaseFour G 3 →
      ∀ B : Subgroup G, IsBZeroMax 3 B → ∀ b ∈ B, b ≠ 1 → ∀ L : Subgroup G,
        IsUpsilonComponent B b L → IsLThreeFour (barOf 3 L) →
        ∀ A F : Subgroup G, IsEkIn 3 2 B A → b ∈ A → (∀ a ∈ A, InducesFieldAut 3 L a) →
          IsElemAbelian 3 F → Nat.card F = 9 → F ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) →
          (∃ y ∈ F ⊓ B, y ≠ 1) → F ⊓ A = ⊥ →
          (∃ f : QuaternionGroup 2 →* autizer (GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G))) F,
            Function.Injective f) →
          ¬ IsStronglyLocallyOneBalanced 3 (F ⊔ A) b L := by
  intro G _ _ m hS hC B hB b hb hb1 L hLU hL34 A F hA hbA hAf hFel hFc hFJ ⟨y, hy, hy1⟩ hFA hQ
  have hJle : GLAPLayer 3 (L ⊓ Subgroup.centralizer (A : Set G)) ≤
      L ⊓ Subgroup.centralizer (A : Set G) := sSup_le fun K hK => hK.1
  have hFL : F ≤ L := hFJ.trans (hJle.trans inf_le_left)
  obtain ⟨hLC, hdisj⟩ := hLU
  have hAN : A ≤ Subgroup.normalizer (L : Set G) := fun a ha => (hAf a ha).fst
  rcases hdisj with ⟨hΛ, hψ⟩ | ⟨D, hD, hDnc⟩
  · exact not_slob_of_branch_a h31 h59 i34i hS hC hB hb hb1 hLC hΛ hψ hL34 hA hAf hFel hFL hy.1 hy.2
      hy1
  · exact not_slob_of_branch_b h191 i34o hS hB.1.1 hb hb1 hLC hL34 hD hDnc hA hbA hAN hFel hFL hy.1
      hy.2 hy1

end Lemma511L34Ns

end CFSG.HardMathSupport.Solomon.LocalBalance
