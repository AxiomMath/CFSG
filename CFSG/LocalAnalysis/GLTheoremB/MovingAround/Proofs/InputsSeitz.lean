module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims138
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SchurFacts
public import CFSG.LocalAnalysis.GL83PartI.I_27_9.Orbits
public import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Induction

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple)
open GL83.CompFam

section General

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem le_glbCore_of_card_stab_le (hp : p.Prime) {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) (k r : ℕ) (hr : 1 ≤ r) (hBk : p ^ (k + r) ≤ Nat.card B)
    (hA : Nat.card (stab B K) ≤ p ^ r * Nat.card (cen B K)) : K ≤ GLBCore p k B := by
  have : Fact p.Prime := ⟨hp⟩
  have h := (isFam_conjSet hB hK).layer_le_centGen k (mem_conjSet_self B K) hr hBk hA
  refine (GL83.CompFam.le_layer (mem_conjSet_self B K)).trans (h.trans ?_)
  refine iSup_le fun E => iSup_le fun hEB => iSup_le fun hEk => ?_
  have hEe : IsElemAbelian p E := elem_mono hB hEB
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hEe
  have hjk : k ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hj ▸ hEk)
  have hrk : k ≤ CFSG.Open.pRank p E := hjk.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEe hj)
  exact inf_le_right.trans
    ((Subgroup.centralizer_le_normalizer (E : Set X)).trans (le_sSup ⟨E, hEB, hrk, rfl⟩))

theorem le_glbCore_two_of_pRank_aut_le_two (hp : p.Prime) {B K : Subgroup X}
    (hB : IsElemAbelian p B) (hB4 : 4 ≤ CFSG.Open.pRank p B) (hK : IsComponentOf K ⊤)
    (haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2) : K ≤ GLBCore p 2 B := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_glbCore_of_card_stab_le hp hB hK 2 2 (by norm_num) ?_ ?_
  · rw [GL83.PiGen.card_eq_pow_pRank hB]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  · exact (card_stab_le hB K).trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos haut))

theorem pRank_top_le_of_forall (hp : p.Prime) {H : Type} [Group H] [Finite H] {m : ℕ}
    (h : ∀ A : Subgroup H, IsElemAbelian p A → CFSG.Open.pRank p A ≤ m) : CFSG.Open.pRank p (⊤ : Subgroup H) ≤ m := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
  rw [GL83.PiGen.card_eq_pow_pRank hE]
  exact Nat.pow_le_pow_right hp.pos (h E hE)

theorem layer_conjSet_eq (B K : Subgroup X) : GL83.CompFam.layer (conjSet B K) = ⨆ g ∈ B, GLBConj g K := by
  apply le_antisymm
  · refine iSup₂_le fun K' hK' => ?_
    obtain ⟨b, hb, rfl⟩ := hK'
    have e : cj b K = GLBConj b⁻¹ K := by
      show K.map (MulAut.conj b).toMonoidHom = K.map (MulAut.conj b⁻¹⁻¹).toMonoidHom
      rw [inv_inv]
    rw [e]
    exact le_iSup₂_of_le (f := fun g (_ : g ∈ B) => GLBConj g K) b⁻¹ (B.inv_mem hb) le_rfl
  · exact iSup₂_le fun g hg => GL83.CompFam.le_layer ⟨g⁻¹, B.inv_mem hg, rfl⟩

theorem isGMinusOne_of_centGenI (hp : p.Prime) {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) (hgen : K ≤ centGenI p (stab B K) K) :
    Lemma1314.IsGMinusOne p B K := by
  have : Fact p.Prime := ⟨hp⟩
  have hF := isFam_conjSet hB hK
  have hK₀ := mem_conjSet_self B K
  have hAB : stab B K ≤ B := inf_le_left
  have hBt : Nat.card B = (stab B K).relIndex B * Nat.card (stab B K) := by
    have h := Subgroup.relIndex_mul_card (H := stab B K) (K := B)
    rw [inf_eq_left.2 hAB] at h
    exact h.symm
  have hBp := GL83.PiGen.card_eq_pow_pRank hB
  obtain ⟨a, -, hta⟩ : ∃ a ≤ CFSG.Open.pRank p B, (stab B K).relIndex B = p ^ a := by
    refine (Nat.dvd_prime_pow hp).1 ?_
    rw [← hBp, hBt]
    exact Dvd.intro _ rfl
  have hlay := hF.layer_le_centGenI a hK₀ (by rw [hBt, hta]) hgen
  unfold Lemma1314.IsGMinusOne Lemma1314.IsGClass Lemma1314.GammaPrimeOf
  rw [← layer_conjSet_eq]
  refine le_antisymm (hlay.trans (iSup_le fun E => ?_)) (iSup₂_le fun A _ => inf_le_right)
  obtain ⟨hEB, hEi⟩ := E.2
  have hEel : IsElemAbelian p E.1 := elem_mono hB hEB
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hEel
  have hjr : CFSG.Open.pRank p B - 1 ≤ j := by
    have h1 : p ^ CFSG.Open.pRank p B ≤ p ^ (j + 1) := by
      calc p ^ CFSG.Open.pRank p B = Nat.card B := hBp.symm
        _ ≤ p * Nat.card E.1 := hEi
        _ = p ^ (j + 1) := by rw [hj, pow_succ, mul_comm]
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
    omega
  have hrk : j ≤ CFSG.Open.pRank p E.1 := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hEel hj
  rw [inf_comm]
  exact le_iSup₂_of_le (f := fun (A : Subgroup X) (_ : A ≤ B ∧ CFSG.Open.pRank p B - 1 ≤ CFSG.Open.pRank p A) =>
    Subgroup.centralizer (A : Set X) ⊓ GL83.CompFam.layer (conjSet B K)) E.1 ⟨hEB, hjr.trans hrk⟩ le_rfl

theorem isGMinusOne_of_card_stab_le (hp : p.Prime) {B K : Subgroup X} (hB : IsElemAbelian p B)
    (hK : IsComponentOf K ⊤) (hA : Nat.card (stab B K) ≤ p * Nat.card (cen B K)) :
    Lemma1314.IsGMinusOne p B K := by
  refine isGMinusOne_of_centGenI hp hB hK ?_
  refine le_trans ?_ (le_centGenI (cen_le_stab B K) hA)
  exact le_inf le_rfl fun x hx => Subgroup.mem_centralizer_iff.2 fun b hb => (mem_cen.1 hb).2 x hx

end General

section AltTools

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem eq_of_card_dvd_two {G : Type*} [Group G] {Z : Subgroup G} (hZ : Nat.card Z ∣ 2) {a b : G}
    (ha : a ∈ Z) (hb : b ∈ Z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  rcases (Nat.dvd_prime Nat.prime_two).1 hZ with h1 | h2
  · obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.1 h1
    exact absurd (congrArg Subtype.val (Subsingleton.elim (⟨a, ha⟩ : Z) 1)) ha1
  · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).1 h2
    have e1 := hy ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
    have e2 := hy ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
    exact congrArg Subtype.val (e1.trans e2.symm)

theorem conj_mem_center {K : Subgroup X} {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X))
    {z : ↥K} (hz : z ∈ Subgroup.center ↥K) :
    ∃ hbz : b * (z : X) * b⁻¹ ∈ K, (⟨b * z * b⁻¹, hbz⟩ : ↥K) ∈ Subgroup.center ↥K := by
  have hbz : b * (z : X) * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hb z).1 z.2
  refine ⟨hbz, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_⟩
  have hg' : b⁻¹ * (g : X) * b ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hb) g).1 g.2
    simpa using this
  have hc : (b⁻¹ * (g : X) * b) * z = z * (b⁻¹ * g * b) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨_, hg'⟩)
  show (g : X) * (b * z * b⁻¹) = b * z * b⁻¹ * g
  calc (g : X) * (b * z * b⁻¹) = b * ((b⁻¹ * g * b) * z) * b⁻¹ := by group
    _ = b * (z * (b⁻¹ * g * b)) * b⁻¹ := by rw [hc]
    _ = b * z * b⁻¹ * g := by group

theorem comm_of_center_card_dvd_two {K : Subgroup X} (hZ2 : Nat.card (Subgroup.center K) ∣ 2)
    {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) {z : ↥K} (hz : z ∈ Subgroup.center ↥K) :
    b * (z : X) = z * b := by
  obtain ⟨hbz, hbzc⟩ := conj_mem_center hb hz
  by_cases hz1 : z = 1
  · subst hz1
    simp
  · have hne : (⟨b * z * b⁻¹, hbz⟩ : ↥K) ≠ 1 := by
      intro h
      have h1 : b * (z : X) * b⁻¹ = 1 := congrArg Subtype.val h
      apply hz1
      apply Subtype.ext
      have h2 : (z : X) = b⁻¹ * (b * z * b⁻¹) * b := by group
      rw [h2, h1]
      simp
    have h3 := eq_of_card_dvd_two hZ2 hbzc hz hne hz1
    have h4 : b * (z : X) * b⁻¹ = z := congrArg Subtype.val h3
    calc b * (z : X) = b * z * b⁻¹ * b := by group
      _ = z * b := by rw [h4]

theorem eq_one_of_conj_eq_mul {G : Type*} [Group G] (hp : p.Prime) (hp2 : p ≠ 2) {w h z : G}
    (hw : w ^ p = 1) (hwh : w * h * w⁻¹ = h * z) (hwz : w * z = z * w) (hz : z ^ 2 = 1) :
    z = 1 := by
  have key : ∀ k : ℕ, w ^ k * h * (w ^ k)⁻¹ = h * z ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hc : w * z ^ k = z ^ k * w := ((Commute.pow_right (show Commute w z from hwz) k)).eq
      calc w ^ (k + 1) * h * (w ^ (k + 1))⁻¹ = w * (w ^ k * h * (w ^ k)⁻¹) * w⁻¹ := by group
        _ = w * (h * z ^ k) * w⁻¹ := by rw [ih]
        _ = (w * h * w⁻¹) * (w * z ^ k * w⁻¹) := by group
        _ = (h * z) * (z ^ k * w * w⁻¹) := by rw [hwh, hc]
        _ = h * z ^ (k + 1) := by rw [mul_inv_cancel_right, pow_succ']; group
  have h1 := key p
  rw [hw, one_mul, inv_one, mul_one] at h1
  have hzp : z ^ p = 1 := mul_left_cancel (h1.symm.trans (mul_one h).symm)
  have hd : orderOf z ∣ Nat.gcd p 2 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_of_pow_eq_one hz)
  rw [(Nat.coprime_primes hp Nat.prime_two).2 hp2, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem eq_one_of_mem_center (hp : p.Prime) {K : Subgroup X}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {x : X} (hxK : x ∈ K) (hxc : ∀ y ∈ K, x * y = y * x)
    (hxp : x ^ p = 1) : x = 1 := by
  have hmem : (⟨x, hxK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (hxc g g.2).symm
  have hd1 : orderOf (⟨x, hxK⟩ : K) ∣ Nat.card (Subgroup.center K) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center K) hmem
  have hd2 : orderOf (⟨x, hxK⟩ : K) ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxp))
  rcases (Nat.dvd_prime hp).1 hd2 with h1 | h1
  · exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  · exact absurd (h1 ▸ hd1) hZ

theorem le_pRank_of_quot (hp : p.Prime) {K : Subgroup X} (hZ : ¬ p ∣ Nat.card (Subgroup.center K))
    {Eb : Subgroup (↥K ⧸ Subgroup.center ↥K)} (hE : IsElemAbelian p Eb) {t : ℕ}
    (ht : Nat.card Eb = p ^ t) : t ≤ CFSG.Open.pRank p K := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, -, hScard⟩ :=
    CFSG.LocalAnalysis.GLTheoremB.exists_elemAbelian_lift (Subgroup.center ↥K) hZ hE
  refine CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_subtype_le S)
    (CFSG.SectionRank.isElemAbelian_map hS _) ?_
  rw [Subgroup.card_map_of_injective K.subtype_injective, hScard, ht]

theorem div_le_pRank_of_alt (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup X}
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {n : ℕ}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) : n / p ≤ CFSG.Open.pRank p K := by
  have h1 := Claims138.le_pRank_of_mulEquiv_alt (X := ↥K ⧸ Subgroup.center ↥K) hp hp2
    (J := ⊤) (Subgroup.topEquiv.trans e)
  obtain ⟨E, -, hE, hcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (↥K ⧸ Subgroup.center ↥K))
  exact h1.trans (le_pRank_of_quot hp hZ hE hcard)

theorem add_le_pRank_of_commute (hp : p.Prime) {E F : Subgroup X} (hE : IsElemAbelian p E)
    (hF : IsElemAbelian p F) (hc : ∀ x ∈ E, ∀ y ∈ F, x * y = y * x) (hd : E ⊓ F = ⊥)
    {a b : ℕ} (ha : Nat.card E = p ^ a) (hb : Nat.card F = p ^ b) :
    a + b ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hEF := CFSG.Open.IsElemAbelian.sup_of_commute hE hF hc
  have hcard := card_sup_of_commute_of_inf_eq_bot hc hd
  rw [ha, hb, ← pow_add] at hcard
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hEF hcard

theorem le_normalizer_of_rank (hp : p.Prime) {B K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) (hrk : CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X))
    (h2 : CFSG.Open.pRank p B < 2 * CFSG.Open.pRank p K) : B ≤ Subgroup.normalizer (K : Set X) := by
  intro b _
  by_contra hbN
  have hK' : IsComponentOf (cj b K) ⊤ := isComponentOf_cj hK b
  have hne : K ≠ cj b K := fun h => hbN (cj_eq_iff_mem_normalizer.1 h.symm)
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne K (cj b K) hK hK' hne
  have hcomm' : ∀ x ∈ K, ∀ y ∈ cj b K, x * y = y * x := by
    intro x hx y hy
    have hxc : x ∈ Subgroup.centralizer (cj b K : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hx
    exact (Subgroup.mem_centralizer_iff.1 hxc y hy).symm
  obtain ⟨E, hEK, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K
  have hE'K : cj b E ≤ cj b K := cj_mono b hEK
  have hE'el : IsElemAbelian p (cj b E) := CFSG.SectionRank.isElemAbelian_map hE _
  have hE'card : Nat.card (cj b E) = p ^ CFSG.Open.pRank p K := by
    show Nat.card (E.map (MulAut.conj b).toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (MulAut.conj b).injective, hEcard]
  have hc : ∀ x ∈ E, ∀ y ∈ cj b E, x * y = y * x := fun x hx y hy =>
    hcomm' x (hEK hx) y (hE'K hy)
  have hd : E ⊓ cj b E = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    refine eq_one_of_mem_center hp hZ (hEK hx.1) (fun y hy => ?_) (hE.2 x hx.1)
    exact (hcomm' y hy x (hE'K hx.2)).symm
  have := add_le_pRank_of_commute hp hE hE'el hc hd hEcard hE'card
  omega

theorem not_pow_three_dvd_10080 (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ^ 3 ∣ 10080 := by
  intro h
  have hp21 : p ≤ 21 := by
    by_contra hlt
    push Not at hlt
    have h22 : 22 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hlt 3
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hp2' := hp.two_le
  interval_cases p
  · exact absurd rfl hp2
  all_goals norm_num at h

end AltTools

section Alt

open Equiv Equiv.Perm MulAction

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem le_glbCore_of_alt_ne_six (hp : p.Prime) (hp2 : p ≠ 2)
    {B K : Subgroup X} (hB : IsElemAbelian p B) (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (hrk : CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X)) (hK : IsComponentOf K ⊤)
    {n : ℕ} (hn6 : n ≠ 6) (hA : IsAltType n (↥K ⧸ Subgroup.center ↥K)) :
    K ≤ GLBCore p 2 B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set m := CFSG.Open.pRank p B with hm
  have hBcard : Nat.card B = p ^ m := GL83.PiGen.card_eq_pow_pRank hB
  by_cases hsmall : Nat.card (stab B K) ≤ p ^ (m - 2) * Nat.card (cen B K)
  · refine le_glbCore_of_card_stab_le hp hB hK 2 (m - 2) (by omega) ?_ hsmall
    rw [hBcard]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  push Not at hsmall
  obtain ⟨e⟩ := hA
  have hq : CFSG.Open.IsQuasisimple K := hK.2.2
  haveI : Group.IsPerfect K := ⟨hq.1⟩
  have hn5 : 5 ≤ n := SchurFacts.five_le_of_isAltType hq ⟨e⟩
  set π := GL83.PiGen.permHom (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e with hπ
  have hAC : Nat.card (stab B K) = Nat.card (cen B K) * Nat.card π.range :=
    GL83.PiGen.card_stab_eq_mul hn5 hn6 e
  have hAel : IsElemAbelian p (stab B K) := elem_mono hB inf_le_left
  have hRel : IsElemAbelian p π.range := GL83.PiGen.isElemAbelian_range hAel π
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hRel
  have hjm : m - 1 ≤ j := by
    have h1 : p ^ (m - 2) * Nat.card (cen B K) < p ^ j * Nat.card (cen B K) := by
      calc p ^ (m - 2) * Nat.card (cen B K) < Nat.card (stab B K) := hsmall
        _ = p ^ j * Nat.card (cen B K) := by rw [hAC, hj, mul_comm]
    have h2 : p ^ (m - 2) < p ^ j := lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 h2
    omega
  have hn7 : n ≠ 7 := by
    rintro rfl
    have hdvd : Nat.card π.range ∣ Nat.card (Perm (Fin 7)) := Subgroup.card_subgroup_dvd_card _
    rw [hj, Nat.card_perm, Nat.card_fin] at hdvd
    have h7 : Nat.factorial 7 = 5040 := by decide
    rw [h7] at hdvd
    exact not_pow_three_dvd_10080 hp hp2
      (((pow_dvd_pow p (by omega)).trans hdvd).trans (by norm_num))
  have hZ2 : Nat.card (Subgroup.center K) ∣ 2 := by
    have h := SchurFacts.card_center_dvd_of_isAltType hq ⟨e⟩
    rwa [if_neg (by omega)] at h
  have hZp : ¬ p ∣ Nat.card (Subgroup.center K) := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (h.trans hZ2))
  have hRA : π.range ≤ alternatingGroup (Fin n) := fun σ hσ =>
    GL83.PiGen.mem_alternatingGroup_of_pow_eq_one hpodd (hRel.2 σ hσ)
  have hjK : j ≤ CFSG.Open.pRank p K := by
    have hEb : IsElemAbelian p ((π.range.subgroupOf (alternatingGroup (Fin n))).map
        e.symm.toMonoidHom) :=
      CFSG.SectionRank.isElemAbelian_map (CFSG.Open.IsElemAbelian.subgroupOf hRel _) _
    refine le_pRank_of_quot hp hZp hEb ?_
    rw [Subgroup.card_map_of_injective e.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRA).toEquiv, hj]
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := le_normalizer_of_rank hp hK hZp hrk (by omega)
  have hstab : stab B K = B := inf_eq_left.2 hBN
  have hAcard : Nat.card (stab B K) = p ^ m := by rw [hstab, hBcard]
  have hker : Nat.card π.ker = Nat.card (cen B K) := by
    have h1 := Subgroup.card_ker_mul_card_range π
    rw [hAC] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hCel : IsElemAbelian p (cen B K) := elem_mono hB inf_le_left
  obtain ⟨c, hc⟩ := GL83.CompFam.exists_card_eq_pow hCel
  have hjc : j + c = m := by
    have h1 : p ^ m = p ^ (c + j) := by rw [← hAcard, hAC, hc, hj, pow_add]
    have := Nat.pow_right_injective hp.two_le h1
    omega
  obtain ⟨EK, hEK, hEKel, hEKcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt K
  have hKc : CFSG.Open.pRank p K + c ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
    refine add_le_pRank_of_commute hp hEKel hCel ?_ ?_ hEKcard hc
    · intro x hx y hy
      exact ((mem_cen.1 hy).2 x (hEK hx)).symm
    · refine eq_bot_iff.2 fun x hx => ?_
      rw [Subgroup.mem_bot]
      exact eq_one_of_mem_center hp hZp (hEK hx.1) (fun y hy => (mem_cen.1 hx.2).2 y hy)
        (hEKel.2 x hx.1)
  have hnK : n / p ≤ CFSG.Open.pRank p K := div_le_pRank_of_alt hp hp2 hZp e
  have hnj : n / p ≤ j := by omega
  have hRcomm : ∀ x ∈ π.range, ∀ y ∈ π.range, x * y = y * x := fun x hx y hy =>
    elem_comm hRel hx hy
  have horb : ∀ ω : Fin n, Nat.card (orbit π.range ω) ≤ p :=
    Claims138.card_orbit_le_of_rank hp hp3 hRel hj hnj
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Fin n, ω₀ ∉ GL83.PiGen.fixSet π.range := by
    by_contra h
    push Not at h
    have hbot : π.range = ⊥ :=
      CFSG.AGLEmbedding.eq_bot_of_forall_apply_eq fun g hg a => (h a) g hg
    have h1 : Nat.card π.range = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hj] at h1
    rcases Nat.pow_eq_one.1 h1 with h | h
    · exact hp.one_lt.ne' h
    · omega
  have horb3 : ∀ ω : Fin n, ω ∉ GL83.PiGen.fixSet π.range → 3 ≤ (orbit π.range ω).ncard := by
    intro ω hω
    obtain ⟨s, hs⟩ := (CFSG.Open.IsElemAbelian.isPGroup hRel).card_orbit ω
    have hle := horb ω
    rw [GL83.PiGen.mem_fixSet] at hω
    push Not at hω
    obtain ⟨g, hg, hgω⟩ := hω
    have h2 : 2 ≤ (orbit π.range ω).ncard := by
      have hsub : ({ω, g ω} : Set (Fin n)) ⊆ orbit π.range ω := by
        intro x hx
        rcases hx with rfl | hx
        · exact mem_orbit_self x
        · rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact mem_orbit ω (⟨g, hg⟩ : π.range)
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
  have hZΓ : ∀ z : ↥K, z ∈ Subgroup.center ↥K → (z : X) ∈ GLBCore p 2 B := by
    intro z hz
    have hzc : (z : X) ∈ Subgroup.centralizer (B : Set X) :=
      Subgroup.mem_centralizer_iff.2 fun b hb => comm_of_center_card_dvd_two hZ2 (hBN hb) hz
    have hN : Subgroup.normalizer (B : Set X) ≤ GLBCore p 2 B := le_sSup ⟨B, le_rfl, by omega, rfl⟩
    exact hN (Subgroup.centralizer_le_normalizer _ hzc)
  set φ : ↥K →* Perm (Fin n) := (alternatingGroup (Fin n)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))) with hφ
  have hAlt : alternatingGroup (Fin n) ≤ ((GLBCore p 2 B).subgroupOf K).map φ := by
    refine Claims138.alternatingGroup_le_of_pairs hRcomm horb3 hω₀ fun ω ω' _ => ?_
    set V := Claims138.pairStab π.range ω ω' with hV
    have hVR : V ≤ π.range := Claims138.pairStab_le π.range ω ω'
    set W : Subgroup ↥(stab B K) := V.comap π with hW
    have hWcard : Nat.card W = Nat.card (cen B K) * Nat.card V := by
      have h1 := Subgroup.card_ker_mul_card_range (π.comp W.subtype)
      have hrange : (π.comp W.subtype).range = V := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, hW, Subgroup.map_comap_eq_self hVR]
      have hle : π.ker ≤ W := fun x hx => by
        show π x ∈ V
        rw [MonoidHom.mem_ker.1 hx]
        exact one_mem V
      have hkerW : (π.comp W.subtype).ker = π.ker.subgroupOf W := by
        ext x
        simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      rw [hrange, hkerW, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hker] at h1
      exact h1.symm
    have hRV : Nat.card π.range ≤ p ^ 2 * Nat.card V := Claims138.card_le_pairStab hRcomm horb ω ω'
    set W' : Subgroup X := W.map (stab B K).subtype with hW'
    have hW'B : W' ≤ B := (Subgroup.map_subtype_le W).trans inf_le_left
    have hW'card : Nat.card W' = Nat.card W :=
      Subgroup.card_map_of_injective (stab B K).subtype_injective
    have hW'el : IsElemAbelian p W' := elem_mono hB hW'B
    have hW'rk : 2 ≤ CFSG.Open.pRank p W' := by
      obtain ⟨w, hw⟩ := GL83.CompFam.exists_card_eq_pow hW'el
      have h1 : p ^ m ≤ p ^ (2 + w) := by
        calc p ^ m = Nat.card (stab B K) := hAcard.symm
          _ = Nat.card (cen B K) * Nat.card π.range := hAC
          _ ≤ Nat.card (cen B K) * (p ^ 2 * Nat.card V) := Nat.mul_le_mul_left _ hRV
          _ = p ^ 2 * (Nat.card (cen B K) * Nat.card V) := by ring
          _ = p ^ (2 + w) := by rw [← hWcard, ← hW'card, hw, pow_add]
      have h2 := (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
      have h3 := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hW'el hw
      omega
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin n) := (GL83.mem_altOn.1 hσ).1
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm ⟨σ, hσA⟩)
    have hek : (e (QuotientGroup.mk k) : Perm (Fin n)) = σ := by
      rw [hk]
      simp
    refine ⟨k, ?_, ?_⟩
    · show (k : X) ∈ GLBCore p 2 B
      have hkC : (k : X) ∈ Subgroup.centralizer (W' : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨y, hy, hspec⟩ :=
          GL83.PiGen.permHom_spec (GL83.PiGen.stab_le_normalizer B K) hn5 hn6 e w k
        have hspec' : π w * (e (QuotientGroup.mk k) : Perm (Fin n)) * (π w)⁻¹ =
            (e (QuotientGroup.mk y) : Perm (Fin n)) := hspec
        have hπw : π w ∈ V := hw
        have hdisj : Perm.Disjoint (π w) σ := by
          intro x
          by_cases hx : x ∈ GL83.PiGen.fixSet V
          · exact Or.inl (hx (π w) hπw)
          · exact Or.inr ((GL83.mem_altOn.1 hσ).2 x hx)
        have hcomm : π w * σ = σ * π w := hdisj.commute.eq
        have hey : (e (QuotientGroup.mk y) : Perm (Fin n)) = σ := by
          rw [← hspec', hek, hcomm, mul_inv_cancel_right]
        have hmk : (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk k :=
          e.injective (Subtype.ext (hey.trans hek.symm))
        have hz : k⁻¹ * y ∈ Subgroup.center ↥K := QuotientGroup.eq.1 hmk.symm
        have hwB : ((w : ↥(stab B K)) : X) ∈ B := (Subgroup.mem_inf.1 w.2).1
        have hwN : ((w : ↥(stab B K)) : X) ∈ Subgroup.normalizer (K : Set X) :=
          (Subgroup.mem_inf.1 w.2).2
        have hwkz : ((w : ↥(stab B K)) : X) * (k : X) * ((w : ↥(stab B K)) : X)⁻¹ =
            (k : X) * ((k⁻¹ * y : ↥K) : X) := by
          rw [← hy]
          simp
        have hwz : ((w : ↥(stab B K)) : X) * ((k⁻¹ * y : ↥K) : X) =
            ((k⁻¹ * y : ↥K) : X) * ((w : ↥(stab B K)) : X) :=
          comm_of_center_card_dvd_two hZ2 hwN hz
        have hz2 : ((k⁻¹ * y : ↥K) : X) ^ 2 = 1 := by
          have hd : orderOf (k⁻¹ * y) ∣ 2 :=
            (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥K) hz).trans hZ2
          have h1 := orderOf_dvd_iff_pow_eq_one.1 hd
          have h2 := congrArg (Subtype.val : ↥K → X) h1
          simpa using h2
        have hz1 := eq_one_of_conj_eq_mul hp hp2 (hB.2 _ hwB) hwkz hwz hz2
        rw [hz1, mul_one] at hwkz
        show ((w : ↥(stab B K)) : X) * (k : X) = (k : X) * ((w : ↥(stab B K)) : X)
        calc ((w : ↥(stab B K)) : X) * (k : X) =
            ((w : ↥(stab B K)) : X) * k * ((w : ↥(stab B K)) : X)⁻¹ * w := by group
          _ = k * w := by rw [hwkz]
      have hN : Subgroup.normalizer (W' : Set X) ≤ GLBCore p 2 B := le_sSup ⟨W', hW'B, hW'rk, rfl⟩
      exact hN (Subgroup.centralizer_le_normalizer _ hkC)
    · exact hek
  intro x hx
  have hφx : φ ⟨x, hx⟩ ∈ alternatingGroup (Fin n) := (e (QuotientGroup.mk ⟨x, hx⟩)).2
  obtain ⟨y, hyΓ, hyx⟩ := hAlt hφx
  have hyx' : (e (QuotientGroup.mk y) : Perm (Fin n)) = e (QuotientGroup.mk ⟨x, hx⟩) := hyx
  have hmk : (QuotientGroup.mk y : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk ⟨x, hx⟩ :=
    e.injective (Subtype.ext hyx')
  have hz := QuotientGroup.eq.1 hmk
  have hx' : x = (y : X) * ((y⁻¹ * ⟨x, hx⟩ : ↥K) : X) := by simp
  rw [hx']
  exact (GLBCore p 2 B).mul_mem hyΓ (hZΓ _ hz)

theorem card_mulAut_alt6_dvd : Nat.card (MulAut (alternatingGroup (Fin 6))) ∣ 1440 := by
  have hinj := CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  set H := (MulAut.conjNormal (H := alternatingGroup (Fin 6)) :
    Perm (Fin 6) →* MulAut ↥(alternatingGroup (Fin 6))).range with hH
  have hHcard : Nat.card H = 720 := by
    rw [hH, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
  have hidx := H.index_mul_card
  rw [hHcard] at hidx
  have hpos : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h12 : H.index = 1 ∨ H.index = 2 := by
    rcases Nat.lt_or_ge H.index 3 with h | h
    · omega
    · exfalso
      have : 3 * 720 ≤ H.index * 720 := Nat.mul_le_mul_right 720 h
      omega
  rw [← hidx]
  rcases h12 with h | h <;> rw [h] <;> norm_num

theorem pRank_aut_le_two_of_alt6 (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K]
    (hperf : commutator K = ⊤) (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 6)) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect K := ⟨hperf⟩
  set ψ : MulAut K →* MulAut ↥(alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K) with hψ
  have hψinj : Function.Injective ψ := (MulAut.congr e).injective.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K)
  refine pRank_top_le_of_forall hp fun A hA => ?_
  have hdvd : Nat.card A ∣ 1440 := by
    rw [← Subgroup.card_map_of_injective hψinj]
    exact (Subgroup.card_subgroup_dvd_card _).trans card_mulAut_alt6_dvd
  by_contra hlt
  push Not at hlt
  rw [GL83.PiGen.card_eq_pow_pRank hA] at hdvd
  exact not_pow_three_dvd_10080 hp hp2 (((pow_dvd_pow p hlt).trans hdvd).trans (by norm_num))

theorem le_glbCore_of_alt (hp : p.Prime) (hp2 : p ≠ 2)
    {B K : Subgroup X} (hB : IsElemAbelian p B) (hB4 : 4 ≤ CFSG.Open.pRank p B)
    (hrk : CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X)) (hK : IsComponentOf K ⊤)
    {n : ℕ} (hA : IsAltType n (↥K ⧸ Subgroup.center ↥K)) : K ≤ GLBCore p 2 B := by
  by_cases hn6 : n = 6
  · subst hn6
    obtain ⟨e⟩ := hA
    exact le_glbCore_two_of_pRank_aut_le_two hp hB hB4 hK
      (pRank_aut_le_two_of_alt6 hp hp2 hK.2.2.1 e)
  · exact le_glbCore_of_alt_ne_six hp hp2 hB hB4 hrk hK hn6 hA

end Alt

@[expose] def Input23_19Chev : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    ∀ B : Subgroup X, IsElemAbelian p B → 4 ≤ CFSG.Open.pRank p B →
      CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥K ⧸ Subgroup.center ↥K)) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) →
      K ≤ GLBCore p 2 B

theorem input23_19_of_chev (hres : Input23_19Chev) :
    Lemma1315b.Input23_19 := by
  intro X _ _ hKX p hp hp2 B hB hB4 hrk K hK htype
  by_cases haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2
  · exact le_glbCore_two_of_pRank_aut_le_two hp hB hB4 hK haut
  · push Not at haut
    rcases htype with ⟨n, hA⟩ | hch | hc
    · exact le_glbCore_of_alt hp hp2 hB hB4 hrk hK hA
    · exact hres X hKX p hp hp2 B hB hB4 hrk K hK hch haut
    · exact absurd (pRank_top_le_of_forall hp hc) (by omega)

section Core

variable {X : Type} [Group X] [Finite X] {p : ℕ}

theorem nonempty_center_quot_equiv {K : Type*} [Group K] (hperf : commutator K = ⊤)
    (N : Subgroup K) [N.Normal] (hN : N ≤ Subgroup.center K) :
    Nonempty (((K ⧸ N) ⧸ Subgroup.center (K ⧸ N)) ≃* (K ⧸ Subgroup.center K)) := by
  haveI : Group.IsPerfect K := ⟨hperf⟩
  have hcenter : (Subgroup.center K).map (QuotientGroup.mk' N) = Subgroup.center (K ⧸ N) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective _) (by simpa only [QuotientGroup.ker_mk'] using hN)
  let equivalence := QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center K) hN
  let centerEquivalence := QuotientGroup.congr
    ((Subgroup.center K).map (QuotientGroup.mk' N)) (Subgroup.center (K ⧸ N)) (MulEquiv.refl _)
    (by simpa using hcenter)
  exact ⟨centerEquivalence.symm.trans equivalence⟩

theorem barX_top_isComponentOf (hp : p.Prime) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hKO : ¬ K ≤ GLAPPrimeCoreOf p (⊤ : Subgroup X)) :
    IsComponentOf (barX p ⊤ K) ⊤ ∧
      Nonempty ((↥(barX p ⊤ K) ⧸ Subgroup.center ↥(barX p ⊤ K)) ≃* (↥K ⧸ Subgroup.center ↥K)) := by
  set T : Subgroup X := ⊤ with hT
  set ψ : ↥K →* ↥T ⧸ GLAPPrimeCore p ↥T :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥T)).comp (Subgroup.inclusion (le_top : K ≤ T)) with hψ
  have hrange : ψ.range = barX p T K := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hq : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  have hker : ψ.ker ≤ Subgroup.center ↥K := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq ψ.ker with h | h
    · exact h
    · exfalso
      apply hKO
      intro k hk
      have hmem : (⟨k, hk⟩ : ↥K) ∈ ψ.ker := by rw [h]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at hmem
      have h2 : (Subgroup.inclusion (le_top : K ≤ T) ⟨k, hk⟩ : ↥T) ∈ GLAPPrimeCore p ↥T :=
        (QuotientGroup.eq_one_iff _).1 hmem
      exact ⟨_, h2, rfl⟩
  let e1 : (↥K ⧸ ψ.ker) ≃* ↥(barX p T K) :=
    (QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)
  have hqbar : CFSG.Open.IsQuasisimple ↥(barX p T K) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1
      (CFSG.ComponentClassification.Quasisimple.central_quotient hq ψ.ker hker)
  have hsn : CFSG.Open.IsSubnormal (barX p T K) ⊤ := by
    have h1 := isSubnormal_comap' T.subtype hK.2.1
    rw [show T.comap T.subtype = ⊤ from Subgroup.subgroupOf_self T] at h1
    have h2 := isSubnormal_map' (QuotientGroup.mk' (GLAPPrimeCore p ↥T)) h1
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  refine ⟨⟨le_top, hsn, hqbar⟩, ?_⟩
  obtain ⟨e2⟩ := nonempty_center_quot_equiv hq.1 ψ.ker hker
  exact ⟨(Lemma1315b.centerQuotEquiv e1.symm).trans e2⟩

@[expose] def Input23_19ChevCore : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → ∀ (p : ℕ), p.Prime → p ≠ 2 →
    GLAPPrimeCore p X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian p B → 4 ≤ CFSG.Open.pRank p B →
      CFSG.Open.pRank p B = CFSG.Open.pRank p (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      (∃ q : ℕ, q.Prime ∧ q ≠ p ∧ IsChevSimple q (↥K ⧸ Subgroup.center ↥K)) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) →
      K ≤ GLBCore p 2 B

theorem input23_19Chev_of_core (hres : Input23_19ChevCore) : Input23_19Chev := by
  intro X _ _ hKX p hp hp2 B hB hB4 hrk K hK hch _
  haveI : Fact p.Prime := ⟨hp⟩
  set T : Subgroup X := ⊤ with hT
  have hBp : IsPGroup p B := CFSG.Open.IsElemAbelian.isPGroup hB
  have hBcard : Nat.card B = p ^ CFSG.Open.pRank p B := GL83.PiGen.card_eq_pow_pRank hB
  have hcore : GLAPPrimeCoreOf p T ≤ GLBCore p 2 B :=
    CFSG.LocalAnalysis.AGL81TheoremC.le_glbCore_of_coprime hB
      (by rw [hBcard]; exact Nat.pow_le_pow_right hp.pos (by omega))
      (not_dvd_card_glaPPrimeCoreOf hp T) ((le_top : B ≤ T).trans (le_normalizer_glaPPrimeCoreOf p T))
  have hnorm : ∀ E : Subgroup X, E ≤ B → 2 ≤ CFSG.Open.pRank p E →
      Subgroup.normalizer (E : Set X) ≤ GLBCore p 2 B := fun E hE hr => le_sSup ⟨E, hE, hr, rfl⟩
  by_cases hKO : K ≤ GLAPPrimeCoreOf p T
  · exact hKO.trans hcore
  obtain ⟨hcomp, ⟨eZ⟩⟩ := barX_top_isComponentOf hp hK hKO
  have hKT : CFSG.Open.IsKGroup ↥T := hKX.subgroup T
  have hKY : CFSG.Open.IsKGroup (↥T ⧸ GLAPPrimeCore p ↥T) := hKT.quotient _
  have hcoreY : GLAPPrimeCore p (↥T ⧸ GLAPPrimeCore p ↥T) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hBel' : IsElemAbelian p (barX p T B) := isElemAbelian_barX hB
  have hrkB : CFSG.Open.pRank p (barX p T B) = CFSG.Open.pRank p B :=
    rank_barX_of_isPGroup hp hBp (le_top : B ≤ T)
  have hrkY : CFSG.Open.pRank p (barX p T B) =
      CFSG.Open.pRank p (⊤ : Subgroup (↥T ⧸ GLAPPrimeCore p ↥T)) := by
    refine le_antisymm (CFSG.SectionRank.pRank_mono hp.one_lt le_top) ?_
    rw [hrkB]
    refine CFSG.SectionRank.pRank_le hp.one_lt fun E _ hE => ?_
    refine Lemma1315b.card_le_barX (fun F hF => ?_) hE
    rw [hrk]
    rw [GL83.PiGen.card_eq_pow_pRank hF]
    exact Nat.pow_le_pow_right hp.pos (CFSG.SectionRank.pRank_mono hp.one_lt le_top)
  have hchY : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧
      IsChevSimple q (↥(barX p T K) ⧸ Subgroup.center ↥(barX p T K)) := by
    obtain ⟨q, hq, hqp, h⟩ := hch
    exact ⟨q, hq, hqp, Lemma1315b.isChevSimple_of_equiv eZ h⟩
  have hgam : barX p T K ≤ GLBCore p 2 (barX p T B) := by
    by_cases haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥(barX p T K))) ≤ 2
    · exact le_glbCore_two_of_pRank_aut_le_two hp hBel' (by rw [hrkB]; exact hB4) hcomp haut
    · push Not at haut
      exact hres _ hKY p hp hp2 hcoreY _ hBel' (by rw [hrkB]; exact hB4) hrkY _ hcomp hchY haut
  exact le_of_barX_le_glbCore hp 2 hBp (le_top : B ≤ T) (le_top : K ≤ T) hnorm hcore hgam

theorem input23_19_of_chevCore (hres : Input23_19ChevCore) :
    Lemma1315b.Input23_19 :=
  input23_19_of_chev (input23_19Chev_of_core hres)

end Core

@[expose] def Input25_5Core : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (p : ℕ), p.Prime → 5 ≤ p → CFSG.Open.IsKGroup Y →
    ∀ (K : Subgroup Y) (d : Y), IsComponentOf K ⊤ → d ∈ Subgroup.normalizer (K : Set Y) →
      orderOf d = p → (∃ name : TauCeti.SporadicName, IsSporType name (↥K ⧸ Subgroup.center ↥K)) →
      (∃ J : Subgroup Y, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set Y)) J ∧
        IsChevSimple 2 (PSimple p J)) →
      (∃ A : Subgroup Y, IsSCp p ⊤ A ∧ d ∈ A ∧ CFSG.Open.pRank p A = 3 ∧
        A ⊓ Subgroup.center Y ≠ ⊥) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) →
      ∀ B : Subgroup Y, IsEkIn p 4 ⊤ B → K ≤ GLBCore p 2 B

theorem input25_5_of_core (hres : Input25_5Core) : Lemma1315b.Input25_5 := by
  intro Y _ _ p hp hp5 hKY K d hK hdK hd hspor hJ hA B hB
  by_cases haut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2
  · obtain ⟨-, hBel, hBcard⟩ := hB
    exact le_glbCore_two_of_pRank_aut_le_two hp hBel
      (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hBel hBcard) hK haut
  · push Not at haut
    exact hres Y p hp hp5 hKY K d hK hdK hd hspor hJ hA haut B hB

theorem exists_complement_elem {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {B C : Subgroup Y}
    (hB : IsElemAbelian p B) (hCB : C ≤ B) :
    ∃ B₁ : Subgroup Y, B₁ ≤ B ∧ B₁ ⊓ C = ⊥ ∧ B₁ ⊔ C = B := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let S : Set (Subgroup Y) := {H | H ≤ B ∧ H ⊓ C = ⊥}
  obtain ⟨H, ⟨hHB, hHC⟩, hmax⟩ := (Set.toFinite S).exists_maximal ⟨⊥, bot_le, bot_inf_eq _⟩
  refine ⟨H, hHB, hHC, le_antisymm (sup_le hHB hCB) fun x hx => ?_⟩
  by_contra hxM
  have hxH : x ∉ H := fun h => hxM (Subgroup.mem_sup_left h)
  have hx1 : x ≠ 1 := fun h => hxH (h ▸ H.one_mem)
  have hxord : orderOf x = p := orderOf_eq_prime (hB.2 x hx) hx1
  have hc : ∀ h ∈ H, ∀ k ∈ Subgroup.zpowers x, h * k = k * h :=
    zpowers_commute fun h hh => elem_comm hB (hHB hh) hx
  have hH' : (H ⊔ Subgroup.zpowers x) ⊓ C = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨h, hh, k, hk, rfl⟩ := (mem_sup_of_commute hc).1 hy.1
    by_cases hk1 : k = 1
    · subst hk1
      rw [mul_one] at hy ⊢
      have : h ∈ H ⊓ C := ⟨hh, hy.2⟩
      rwa [hHC] at this
    · exfalso
      have hkx : Subgroup.zpowers k = Subgroup.zpowers x := by
        refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hk) ?_
        have hkp : k ^ p = 1 := by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hB.2 x hx, one_zpow]
        rw [Nat.card_zpowers, Nat.card_zpowers, hxord, orderOf_eq_prime hkp hk1]
      have hkHC : k ∈ H ⊔ C := by
        have : k = h⁻¹ * (h * k) := by group
        rw [this]
        exact (H ⊔ C).mul_mem (Subgroup.mem_sup_left (H.inv_mem hh)) (Subgroup.mem_sup_right hy.2)
      apply hxM
      have hxk : x ∈ Subgroup.zpowers k := hkx ▸ Subgroup.mem_zpowers x
      exact (Subgroup.zpowers_le.2 hkHC) hxk
  have hle := hmax ⟨sup_le hHB ((Subgroup.zpowers_le).2 hx), hH'⟩ le_sup_left
  exact hxH (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))

@[expose] def Input23_10Faith : Prop :=
  ∀ (p q : ℕ), p.Prime → 5 ≤ p → q.Prime → q ≠ p →
    ∀ (Y : Type) [Group Y] [Finite Y], GLAPPrimeCore p Y = ⊥ →
      ∀ (K B : Subgroup Y), IsComponentOf K ⊤ → IsElemAbelian p B →
        B ≤ Subgroup.normalizer (K : Set Y) → B ⊓ Subgroup.centralizer (K : Set Y) = ⊥ →
        p < Nat.card B → Nat.card B ≤ p ^ 3 → IsLieChar (· = q) ↥K → (p = 5 → ¬ Lemma1314.I2310Exc5 K) →
        Lemma1314.IsGMinusOne p B K

theorem isGMinusOne_of_faithful_le {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {K A : Subgroup Y}
    (hA : IsElemAbelian p A) (hAN : A ≤ Subgroup.normalizer (K : Set Y))
    (hcard : p * Nat.card ↥(A ⊓ Subgroup.centralizer (K : Set Y)) < Nat.card A)
    (hres : ∀ B₁ : Subgroup Y, IsElemAbelian p B₁ → B₁ ≤ Subgroup.normalizer (K : Set Y) →
      B₁ ⊓ Subgroup.centralizer (K : Set Y) = ⊥ → p < Nat.card B₁ → Nat.card B₁ ≤ Nat.card A →
        Lemma1314.IsGMinusOne p B₁ K) :
    Lemma1314.IsGMinusOne p A K := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hKfix : ∀ A' : Subgroup Y, A' ≤ Subgroup.normalizer (K : Set Y) →
      (⨆ g ∈ A', GLBConj g K) = K := by
    intro A' hA'
    apply le_antisymm
    · exact iSup₂_le fun g hg => (gLBConj_eq_of_mem_normalizer (hA' hg)).le
    · exact le_iSup₂_of_le (f := fun g (_ : g ∈ A') => GLBConj g K) 1 (one_mem _) (gLBConj_one K).ge
  set C := A ⊓ Subgroup.centralizer (K : Set Y) with hC
  have hCB : C ≤ A := inf_le_left
  obtain ⟨B₁, hB₁B, hB₁C, hB₁sup⟩ := exists_complement_elem hp hA hCB
  have hB₁el : IsElemAbelian p B₁ := elem_mono hA hB₁B
  have hcomm : ∀ x ∈ B₁, ∀ y ∈ C, x * y = y * x := fun x hx y hy =>
    elem_comm hA (hB₁B hx) (hCB hy)
  have hfaith : B₁ ⊓ Subgroup.centralizer (K : Set Y) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [← hB₁C]
    exact ⟨hx.1, hB₁B hx.1, hx.2⟩
  have hcardB : Nat.card A = Nat.card B₁ * Nat.card C := by
    rw [← card_sup_of_commute_of_inf_eq_bot hcomm hB₁C, hB₁sup]
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hB₁card : p < Nat.card B₁ := by
    rw [hcardB] at hcard
    by_contra hle
    push Not at hle
    have := Nat.mul_le_mul_right (Nat.card C) hle
    linarith
  have hG := hres B₁ hB₁el (hB₁B.trans hAN) hfaith hB₁card (Subgroup.card_le_of_le hB₁B)
  unfold Lemma1314.IsGMinusOne Lemma1314.IsGClass Lemma1314.GammaPrimeOf at hG ⊢
  rw [hKfix B₁ (hB₁B.trans hAN)] at hG
  rw [hKfix A hAN]
  refine le_antisymm (hG.le.trans (iSup₂_le fun E₁ hE₁ => ?_)) (iSup₂_le fun A' _ => inf_le_right)
  obtain ⟨hE₁B₁, hE₁r⟩ := hE₁
  have hE₁el : IsElemAbelian p E₁ := elem_mono hB₁el hE₁B₁
  have hEB : E₁ ⊔ C ≤ A := sup_le (hE₁B₁.trans hB₁B) hCB
  have hEel : IsElemAbelian p (E₁ ⊔ C) := elem_mono hA hEB
  have hE₁C : E₁ ⊓ C = ⊥ := le_bot_iff.1 (hB₁C ▸ inf_le_inf_right C hE₁B₁)
  have hcardE : Nat.card (E₁ ⊔ C : Subgroup Y) = Nat.card E₁ * Nat.card C :=
    card_sup_of_commute_of_inf_eq_bot (fun x hx y hy => hcomm x (hE₁B₁ hx) y hy) hE₁C
  have hrk : CFSG.Open.pRank p A - 1 ≤ CFSG.Open.pRank p (E₁ ⊔ C) := by
    have h1 : Nat.card B₁ ≤ p * Nat.card E₁ := by
      rw [GL83.PiGen.card_eq_pow_pRank hB₁el, GL83.PiGen.card_eq_pow_pRank hE₁el]
      calc p ^ CFSG.Open.pRank p B₁ ≤ p ^ (CFSG.Open.pRank p E₁ + 1) :=
            Nat.pow_le_pow_right hp.pos (by omega)
        _ = p * p ^ CFSG.Open.pRank p E₁ := by ring
    have h2 : p ^ CFSG.Open.pRank p A ≤ p ^ (CFSG.Open.pRank p (E₁ ⊔ C) + 1) := by
      rw [← GL83.PiGen.card_eq_pow_pRank hA, pow_succ, ← GL83.PiGen.card_eq_pow_pRank hEel, hcardB,
        hcardE]
      calc Nat.card B₁ * Nat.card C ≤ (p * Nat.card E₁) * Nat.card C := Nat.mul_le_mul_right _ h1
        _ = Nat.card E₁ * Nat.card C * p := by ring
    have := (Nat.pow_le_pow_iff_right hp.one_lt).1 h2
    omega
  refine le_iSup₂_of_le (f := fun (A' : Subgroup Y) (_ : A' ≤ A ∧ CFSG.Open.pRank p A - 1 ≤
    CFSG.Open.pRank p A') => Subgroup.centralizer (A' : Set Y) ⊓ K) (E₁ ⊔ C) ⟨hEB, hrk⟩ ?_
  rintro x ⟨hxE, hxK⟩
  refine ⟨?_, hxK⟩
  have hle : E₁ ⊔ C ≤ Subgroup.centralizer ({x} : Set Y) := by
    refine sup_le (fun e he => ?_) (fun c hc => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxE e he)
    · exact Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hc.2 x hxK).symm)
  show x ∈ Subgroup.centralizer ((E₁ ⊔ C : Subgroup Y) : Set Y)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

theorem input23_10_of_faith (hres : Input23_10Faith) : Lemma1314.Input23_10 := by
  intro p q hp hp5 hq hqp Y _ _ hcore K B hK hB hB3 hlie hexc
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hsmall : Nat.card (stab B K) ≤ p * Nat.card (cen B K)
  · exact isGMinusOne_of_card_stab_le hp hB hK hsmall
  push Not at hsmall
  refine isGMinusOne_of_centGenI hp hB hK ?_
  have hAel : IsElemAbelian p (stab B K) := elem_mono hB inf_le_left
  have hAN : stab B K ≤ Subgroup.normalizer (K : Set Y) := inf_le_right
  have hcen : stab B K ⊓ Subgroup.centralizer (K : Set Y) = cen B K := by
    show B ⊓ Subgroup.normalizer (K : Set Y) ⊓ Subgroup.centralizer (K : Set Y) =
      B ⊓ Subgroup.centralizer (K : Set Y)
    rw [inf_assoc, inf_eq_right.2 (Subgroup.centralizer_le_normalizer (K : Set Y))]
  have hA3 : Nat.card (stab B K) ≤ p ^ 3 := (Subgroup.card_le_of_le inf_le_left).trans hB3
  have h : Lemma1314.IsGMinusOne p (stab B K) K :=
    isGMinusOne_of_faithful_le hp hAel hAN (by rw [hcen]; exact hsmall)
      fun B₁ hB₁ hB₁N hfaith hB₁card hB₁le =>
        hres p q hp hp5 hq hqp Y hcore K B₁ hK hB₁ hB₁N hfaith hB₁card (hB₁le.trans hA3) hlie hexc
  have hKA : (⨆ g ∈ stab B K, GLBConj g K) = K := by
    apply le_antisymm
    · exact iSup₂_le fun g hg => (gLBConj_eq_of_mem_normalizer (hAN hg)).le
    · exact le_iSup₂_of_le (f := fun g (_ : g ∈ stab B K) => GLBConj g K) 1 (one_mem _)
        (gLBConj_one K).ge
  unfold Lemma1314.IsGMinusOne Lemma1314.IsGClass Lemma1314.GammaPrimeOf at h
  rw [hKA] at h
  refine h.le.trans (iSup₂_le fun E hE => ?_)
  rw [inf_comm]
  refine le_centGenI hE.1 ?_
  have hEel : IsElemAbelian p E := elem_mono hAel hE.1
  have hEr := hE.2
  rw [GL83.PiGen.card_eq_pow_pRank hAel, GL83.PiGen.card_eq_pow_pRank hEel]
  calc p ^ CFSG.Open.pRank p (stab B K) ≤ p ^ (CFSG.Open.pRank p E + 1) :=
        Nat.pow_le_pow_right hp.pos (by omega)
    _ = p * p ^ CFSG.Open.pRank p E := by ring

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz

end
