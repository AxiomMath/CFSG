module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Trans
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step15

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Sec2

theorem mem_normalizer_of_forall_conj_mem {X : Subgroup G} {w : G}
    (h : ∀ x ∈ X, w * x * w⁻¹ ∈ X) : w ∈ normalizer (X : Set G) :=
  AS76b.mem_normalizer_of_map_conj_le (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

theorem mem_normalizer_of_mem_centralizerMod {X Y Z : Subgroup G} (hZY : Z ≤ Y) {c : G}
    (hc : c ∈ centralizerMod X Y Z) : c ∈ normalizer (Y : Set G) := by
  have h : c⁻¹ ∈ normalizer (Y : Set G) := mem_normalizer_of_forall_conj_mem fun y hy => by
    have := Y.mul_mem hy (hZY ((mem_centralizerMod.mp hc).2.2 y hy))
    simpa [mul_assoc] using this
  simpa using inv_mem h

theorem mul_mul_eq_one_and_commutator_eq_one {M : Type*} [Group M] {s₁ t₁ s₂ t₂ : M}
    (hs : s₁ * s₁ = 1) (ht : t₁ * t₁ = 1) (h₁₁ : Commute s₁ t₁) (h₁₂ : Commute s₁ t₂)
    (h₂₁ : Commute s₂ t₁) (hss : Commute s₁ s₂) (htt : Commute t₁ t₂) :
    s₁ * t₁ * (s₁ * t₁) = 1 ∧ s₁ * t₁ * (s₂ * t₂) * (s₁ * t₁)⁻¹ * (s₂ * t₂)⁻¹ = 1 := by
  have hc : Commute (s₁ * t₁) (s₂ * t₂) :=
    (hss.mul_right h₁₂).mul_left (h₂₁.symm.mul_right htt)
  constructor
  · calc s₁ * t₁ * (s₁ * t₁) = s₁ * (t₁ * s₁) * t₁ := by group
      _ = s₁ * (s₁ * t₁) * t₁ := by rw [← h₁₁.eq]
      _ = s₁ * s₁ * (t₁ * t₁) := by group
      _ = 1 := by rw [hs, ht, one_mul]
  · rw [hc.eq]
    group

end Sec2

section Points

variable {R E H : Subgroup G} {T : Subgroup (Equiv.Perm ↥(pointsIn R E))}

theorem PointsData.mem_of_pointsAction_eq_one (hD : PointsData R E H)
    (hCE : ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ E)
    {k : ↥(normalizer (E : Set G))} (hk : pointsAction R E k = 1) {n : ℕ}
    (hkn : (k : G) ^ 2 ^ n = 1) : (k : G) ∈ E :=
  hCE _ (hD.mem_centralizer_of_pow_eq_one k.2 (mem_normalizer_of_pointsAction_eq_one hk) hkn) n
    hkn

theorem PointsData.normalizer_le_normalizer (hD : PointsData R E H) :
    normalizer (E : Set G) ≤ normalizer (H : Set G) := fun n hn =>
  Sec2.mem_normalizer_of_forall_conj_mem fun h hh => by
    by_contra hnot
    obtain ⟨Q, hQ, hQh⟩ := hD.cover _ ((mem_normalizer_iff.mp hn h).mp (hD.H_le hh)) hnot
    have hmem : h ∈ rightConjugate Q n ⊓ H := ⟨(mem_rightConjugate_iff Q n h).mpr hQh, hh⟩
    rw [hD.inf_H _ (rightConjugate_mem_pointsIn hQ hn), mem_bot] at hmem
    rw [hmem, mul_one, mul_inv_cancel] at hnot
    exact hnot H.one_mem

omit [Finite G] in
theorem TranslationData.pointsAction_mem (hT : TranslationData R E T) (hRE : R ≤ E)
    {p : ↥(normalizer (E : Set G))} (hp : (p : G) ∈ sec2P E) : pointsAction R E p ∈ T :=
  hT.map_le hRE (Sec2.isPGroup_sec2P E) (Sec2.normalizer_le_normalizer_sec2P E) ⟨p, hp, rfl⟩

theorem sec2P_inf_normalizer_eq (hD : PointsData R E H) (hT : TranslationData R E T)
    (hCE : ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ E)
    (hE2 : IsPGroup 2 E) : sec2P E ⊓ normalizer (R : Set G) = E := by
  have hX2 : IsPGroup 2 (sec2P E ⊓ normalizer (R : Set G) : Subgroup G) :=
    (Sec2.isPGroup_sec2P E).to_le inf_le_left
  have hle := hD.le_centralizer hT hX2 (inf_le_left.trans (Sec2.sec2P_le E)) inf_le_right
    fun n hn => inf_normalizer_le_normalizer_inf
      ⟨Sec2.normalizer_le_normalizer_sec2P E hn.1, le_normalizer hn.2⟩
  refine le_antisymm (fun x hx => ?_) (le_inf (Sec2.le_sec2P hE2 le_normalizer le_rfl)
    fun e he => centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      hD.comm r (hD.R_le hr) e he))
  obtain ⟨n, hn⟩ := hX2 ⟨x, hx⟩
  exact hCE x (hle hx) n (by simpa using congrArg Subtype.val hn)

theorem PointsData.mem_of_apply_eq (hD : PointsData R E H) (hT : TranslationData R E T)
    (hCE : ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ E)
    {p : ↥(normalizer (E : Set G))} (hp : (p : G) ∈ sec2P E) {Q : ↥(pointsIn R E)}
    (hQ : pointsAction R E p Q = Q) : (p : G) ∈ E := by
  obtain ⟨n, hn⟩ := Sec2.isPGroup_sec2P E ⟨(p : G), hp⟩
  exact hD.mem_of_pointsAction_eq_one hCE
    (hT.eq_one_of_apply_eq (hT.pointsAction_mem hD.R_le hp) hQ) (n := n)
    (by simpa using congrArg Subtype.val hn)

theorem PointsData.sq_mem_and_commutator_mem (hD : PointsData R E H)
    (hT : TranslationData R E T)
    (hCE : ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ E) {p q : G}
    (hp : p ∈ sec2P E) (hq : q ∈ sec2P E) : p * p ∈ E ∧ p * q * p⁻¹ * q⁻¹ ∈ E := by
  have hker : ∀ x : ↥(normalizer (E : Set G)), (x : G) ∈ sec2P E → pointsAction R E x = 1 →
      (x : G) ∈ E := fun x hx h1 => by
    obtain ⟨n, hn⟩ := Sec2.isPGroup_sec2P E ⟨(x : G), hx⟩
    exact hD.mem_of_pointsAction_eq_one hCE h1 (n := n) (by simpa using congrArg Subtype.val hn)
  obtain ⟨a, rfl⟩ : ∃ a : ↥(normalizer (E : Set G)), (a : G) = p :=
    ⟨⟨p, Sec2.sec2P_le E hp⟩, rfl⟩
  obtain ⟨b, rfl⟩ : ∃ b : ↥(normalizer (E : Set G)), (b : G) = q :=
    ⟨⟨q, Sec2.sec2P_le E hq⟩, rfl⟩
  have haT : pointsAction R E a ∈ T := hT.pointsAction_mem hD.R_le hp
  have hbT : pointsAction R E b ∈ T := hT.pointsAction_mem hD.R_le hq
  have hab : pointsAction R E a * pointsAction R E b = pointsAction R E b * pointsAction R E a :=
    congrArg Subtype.val (hT.elem.1.is_comm.comm ⟨_, haT⟩ ⟨_, hbT⟩)
  refine ⟨hker (a * a) ((sec2P E).mul_mem hp hp) ?_, hker (a * b * a⁻¹ * b⁻¹)
    ((sec2P E).mul_mem ((sec2P E).mul_mem ((sec2P E).mul_mem hp hq) ((sec2P E).inv_mem hp))
      ((sec2P E).inv_mem hq)) ?_⟩
  · rw [map_mul, ← sq]
    exact hT.elem.2 _ haT
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hab]
    group

theorem PointsData.commutator_mem (hD : PointsData R E H) (hT : TranslationData R E T)
    (hCE : ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ E)
    (hE : IsElemAbelian 2 E) {e p : G} (he : e ∈ E) (hp : p ∈ sec2P E) :
    e⁻¹ * p⁻¹ * e * p ∈ H := by
  have hpN := Sec2.sec2P_le E hp
  have hpE : p⁻¹ * e * p ∈ E := by
    have := (mem_normalizer_iff.mp (inv_mem hpN) e).mp he
    simpa using this
  have hinv : ∀ x ∈ E, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hE.2 x hx)
  have hwE : e⁻¹ * p⁻¹ * e * p ∈ E := by
    have := E.mul_mem (E.inv_mem he) hpE
    simpa [mul_assoc] using this
  by_contra hw
  obtain ⟨Q, hQ, hwQ⟩ := hD.cover _ hwE hw
  have hpp := (hD.sq_mem_and_commutator_mem hT hCE hp hp).1
  have hxy : p * e * p⁻¹ = p⁻¹ * e * p := by
    calc p * e * p⁻¹ = p * p * (p⁻¹ * e * p) * (p * p)⁻¹ := by group
      _ = p⁻¹ * e * p * (p * p) * (p * p)⁻¹ := by rw [hD.comm _ hpp _ hpE]
      _ = p⁻¹ * e * p := by group
  have hfix : p * (e⁻¹ * p⁻¹ * e * p) * p⁻¹ = e⁻¹ * p⁻¹ * e * p := by
    calc p * (e⁻¹ * p⁻¹ * e * p) * p⁻¹ = (p * e * p⁻¹)⁻¹ * e := by group
      _ = (p⁻¹ * e * p)⁻¹ * e := by rw [hxy]
      _ = p⁻¹ * e * p * e := by rw [hinv _ hpE]
      _ = e * (p⁻¹ * e * p) := hD.comm _ hpE _ he
      _ = e⁻¹ * (p⁻¹ * e * p) := by rw [hinv _ he]
      _ = e⁻¹ * p⁻¹ * e * p := by group
  have hw1 : e⁻¹ * p⁻¹ * e * p ≠ 1 := fun h => hw (by rw [h]; exact H.one_mem)
  have hQQ : rightConjugate Q p = Q := by
    by_contra hne
    have hmem : e⁻¹ * p⁻¹ * e * p ∈ rightConjugate Q p ⊓ Q :=
      ⟨(mem_rightConjugate_iff Q p _).mpr (by rw [hfix]; exact hwQ), hwQ⟩
    rw [hD.disj _ (rightConjugate_mem_pointsIn hQ hpN) _ hQ hne, mem_bot] at hmem
    exact hw1 hmem
  have hfixQ : pointsAction R E ⟨p⁻¹, inv_mem hpN⟩ ⟨Q, hQ⟩ = ⟨Q, hQ⟩ := by
    apply Subtype.ext
    rw [coe_pointsAction_apply]
    show rightConjugate Q p⁻¹⁻¹ = Q
    rw [inv_inv, hQQ]
  have hpE' : p⁻¹ ∈ E := hD.mem_of_apply_eq hT hCE (p := ⟨p⁻¹, inv_mem hpN⟩) (inv_mem hp) hfixQ
  have hpE'' : p ∈ E := by simpa using E.inv_mem hpE'
  apply hw1
  calc e⁻¹ * p⁻¹ * e * p = e⁻¹ * p⁻¹ * (e * p) := by group
    _ = e⁻¹ * p⁻¹ * (p * e) := by rw [hD.comm _ he _ hpE'']
    _ = 1 := by group

omit [Finite G] in
theorem TranslationData.relIndex_eq_card (hT : TranslationData R E T) (hD : PointsData R E H)
    {X : Subgroup G} (hXN : X ≤ normalizer (E : Set G))
    (hker : ∀ x : ↥(normalizer (E : Set G)), (x : G) ∈ X → pointsAction R E x = 1 →
      (x : G) ∈ E)
    (hXT : ∀ x : ↥(normalizer (E : Set G)), (x : G) ∈ X → pointsAction R E x ∈ T)
    (Ω : Set ↥(pointsIn R E))
    (hΩ : ∀ x : ↥(normalizer (E : Set G)), (x : G) ∈ X →
      pointsAction R E x ⟨R, hD.self_mem⟩ ∈ Ω)
    (hΩ' : ∀ Q ∈ Ω, ∃ x : ↥(normalizer (E : Set G)), (x : G) ∈ X ∧
      pointsAction R E x ⟨R, hD.self_mem⟩ = Q) :
    E.relIndex X = Nat.card Ω := by
  set p₀ : ↥(pointsIn R E) := ⟨R, hD.self_mem⟩
  set f : ↥X →* Equiv.Perm ↥(pointsIn R E) := (pointsAction R E).comp (inclusion hXN)
  have hker' : f.ker = E.subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact ⟨fun h => hker (inclusion hXN x) x.2 h, fun h =>
      pointsAction_eq_one_of_mem_centralizer (c := inclusion hXN x)
        (mem_centralizer_iff.mpr fun e he => hD.comm e he x h)⟩
  have hmaps : ∀ σ ∈ f.range, σ p₀ ∈ Ω := by
    rintro _ ⟨x, rfl⟩
    exact hΩ (inclusion hXN x) x.2
  have hrangeT : ∀ σ ∈ f.range, σ ∈ T := by
    rintro _ ⟨x, rfl⟩
    exact hXT (inclusion hXN x) x.2
  rw [Subgroup.relIndex, ← hker', index_ker]
  refine Nat.card_congr (Equiv.ofBijective
    (fun σ => ⟨(σ : Equiv.Perm ↥(pointsIn R E)) p₀, hmaps σ σ.2⟩) ⟨fun σ₁ σ₂ h => ?_, fun Q => ?_⟩)
  · have h' : (σ₁ : Equiv.Perm ↥(pointsIn R E)) p₀ = (σ₂ : Equiv.Perm ↥(pointsIn R E)) p₀ :=
      congrArg Subtype.val h
    have h1 := hT.eq_one_of_apply_eq (T.mul_mem (T.inv_mem (hrangeT _ σ₂.2)) (hrangeT _ σ₁.2))
      (p := p₀) (by rw [Equiv.Perm.mul_apply, h']; exact Equiv.Perm.inv_eq_iff_eq.mpr rfl)
    rw [inv_mul_eq_one] at h1
    exact Subtype.ext h1.symm
  · obtain ⟨x, hxX, hx⟩ := hΩ' Q Q.2
    exact ⟨⟨pointsAction R E x, ⟨(x : G), hxX⟩, rfl⟩, Subtype.ext hx⟩

end Points

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

theorem exists_pointsData
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    PointsData R E (E ⊓ A) ∧
      ∃ T : Subgroup (Equiv.Perm ↥(pointsIn R E)), TranslationData R E T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcover, hdisj, h16, -, -⟩ := step15_points h11 hE16 hF hL hodd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  refine ⟨⟨hcomm, inf_le_left, hF.R_le_E, fun Q hQ => ?_, fun e he heH => hcover e he
    fun heA => heH ⟨he, heA⟩, hdisj, fun e he => ?_, ?_, hF.elemR, hF.cardR⟩, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    by_cases hQR : Q = R
    · subst hQR
      rw [← hRA1]
      exact ⟨hx.1, hx.2.2⟩
    · rw [← inf_eq_bot_of_mem_pointsIn_frame h11 hE16 hF hL hodd Q hQ hQR]
      exact ⟨hx.1, hx.2.2⟩
  · obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRA hF.R_le_E hF.E_le he
    exact ⟨a, ha, r, hr, rfl⟩
  · have hne : E ⊓ A ≠ ⊥ := fun h => by
      rw [h, card_bot] at hEA16
      omega
    obtain ⟨⟨h, hh⟩, hh1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    exact ⟨h, hh, fun h' => hh1 (Subtype.ext h')⟩
  · obtain ⟨T, hTr, hTn, hTe, hT16, hTt⟩ :=
      exists_translations h11 hE16 ostromWagnerAG24 hF hL hodd
    exact ⟨T, h16, fun p₁ p₂ q₁ q₂ hp hq =>
      exists_pointsAction_eq_pair h11 hE16 hF hL hodd hp hq, hTr, hTn, hTe, hT16, hTt⟩

theorem mem_of_mem_centralizer_of_frame (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    ∀ c ∈ centralizer (E : Set G), ∀ n : ℕ, c ^ 2 ^ n = 1 → c ∈ E := by
  obtain ⟨hCEO, -, -⟩ := centralizer_eq_sup_oddCoreIn hF hL hodd
  intro c hc n hn
  rw [hCEO] at hc
  exact Sec2.mem_of_mem_sup_of_odd' (isPGroup_two_of_isElemAbelian hF.elemE)
    (AS76b.odd_card_oddCoreIn _) (AS76b.oddCoreIn_le _) hc hn

theorem exists_mem_sec2P_rightConjugate_eq
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    ∀ Q ∈ pointsIn R E, ∃ p ∈ sec2P E, rightConjugate R p = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, P₀, P', hP₀N, hNP₀, -, -, -, htr, hP'2, hP'P₀, hP₀eq, hOP'⟩ :=
    step15_of_frame h11 hE16 hF hL hodd
  have hOodd := AS76b.odd_card_oddCoreIn (centralizer (E : Set G))
  have hP'n : normalizer (E : Set G) ≤ normalizer (P' : Set G) := fun n hn =>
    Sec2.mem_normalizer_of_forall_conj_mem fun x hx => by
      obtain ⟨k, hk⟩ := hP'2 ⟨x, hx⟩
      have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hmem : n * x * n⁻¹ ∈ P' ⊔ AS76b.oddCoreIn (centralizer (E : Set G)) := by
        rw [sup_comm, ← hP₀eq]
        exact (mem_normalizer_iff.mp (hNP₀ hn) x).mp (hP'P₀ hx)
      exact Sec2.mem_of_mem_sup_of_odd' hP'2 hOodd hOP' hmem (k := k)
        (by rw [conj_pow, hxk, mul_one, mul_inv_cancel])
  have hP'P : P' ≤ sec2P E := Sec2.le_sec2P hP'2 (hP'P₀.trans hP₀N) hP'n
  intro Q hQ
  obtain ⟨p, hp, hpQ⟩ := htr Q hQ
  have hp' : p ∈ ((AS76b.oddCoreIn (centralizer (E : Set G)) ⊔ P' : Subgroup G) : Set G) := by
    rw [← hP₀eq]
    exact hp
  rw [coe_mul_of_left_le_normalizer_right _ _ (hOP'.trans (centralizer_le_normalizer _))] at hp'
  obtain ⟨o, ho, p', hp'', rfl⟩ := hp'
  refine ⟨p', hP'P hp'', ?_⟩
  have hoR : o ∈ normalizer (R : Set G) := centralizer_le_normalizer _ (mem_centralizer_iff.mpr
    fun r hr => mem_centralizer_iff.mp (AS76b.oddCoreIn_le _ ho) r (hF.R_le_E hr))
  rw [← hpQ, ← rightConjugate_mul, (rightConjugate_eq_self_iff R o).mpr hoR]

theorem card_points_le_inf (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    Nat.card {Q : ↥(pointsIn R E) | (Q : Subgroup G) ≤ E ⊓ F} = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hRgEF : rightConjugate R g ≤ E ⊓ F := hF.inf_eq ▸ le_sup_right
  set pR : ↥(pointsIn R E) := ⟨R, self_mem_pointsIn hF.R_le_E⟩
  set pRg : ↥(pointsIn R E) := ⟨rightConjugate R g, hRgEF.trans inf_le_left, g, rfl⟩
  have hne : pR ≠ pRg := fun h => rightConjugate_ne_of_frame hF (congrArg Subtype.val h).symm
  set Ω := {Q : ↥(pointsIn R E) | (Q : Subgroup G) ≤ E ⊓ F}
  have hΩ : Ω = pointLine R E pR pRg := by
    ext Q
    show (Q : Subgroup G) ≤ E ⊓ F ↔ (Q : Subgroup G) ≤ R ⊔ rightConjugate R g
    rw [hF.inf_eq]
  have hle : Ω.ncard ≤ 4 := by
    rw [hΩ]
    exact ncard_pointLine_le hKte hR hF.elemE hF.R_le_E hF.E_le hRA1
      (inf_eq_bot_of_mem_pointsIn_frame h11 hE16 hF hL hodd) hF.cardE hF.cardR hne
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, h₁, h₂, h₁R, h₂R, h₁g, h₂g, h₁₂⟩ :=
    exists_four_points h11 hE16 hF hL hodd
  set p₁ : ↥(pointsIn R E) := ⟨Q₁, hQ₁⟩
  set p₂ : ↥(pointsIn R E) := ⟨Q₂, hQ₂⟩
  have hsub : ({pR, pRg, p₁, p₂} : Set ↥(pointsIn R E)) ⊆ Ω := by
    intro Q hQ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hQ
    rcases hQ with rfl | rfl | rfl | rfl
    · exact hREF
    · exact hRgEF
    · exact h₁
    · exact h₂
  have hcard : ({pR, pRg, p₁, p₂} : Set ↥(pointsIn R E)).ncard = 4 := by
    have h3 : p₁ ≠ p₂ := fun h => h₁₂ (congrArg Subtype.val h)
    have h2 : pRg ∉ ({p₁, p₂} : Set ↥(pointsIn R E)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => h₁g (congrArg Subtype.val h).symm,
        fun h => h₂g (congrArg Subtype.val h).symm⟩
    have h1 : pR ∉ ({pRg, p₁, p₂} : Set ↥(pointsIn R E)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, fun h => h₁R (congrArg Subtype.val h).symm,
        fun h => h₂R (congrArg Subtype.val h).symm⟩
    rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]
  have hge := Set.ncard_le_ncard hsub (Set.toFinite Ω)
  rw [Nat.card_coe_set_eq]
  omega

theorem le_centralizerMod (hF : Frame G A A R g E F) :
    E ≤ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZEF : sec2Z A E F ≤ E ⊓ F := by rw [hF.sec2Z_eq]; exact inf_le_left
  intro e he
  refine mem_centralizerMod.mpr ⟨Sec2.le_sec2P (isPGroup_two_of_isElemAbelian hF.elemE)
    le_normalizer le_rfl he, centralizer_le_normalizer _ (mem_centralizer_iff.mpr
      fun z hz => hcomm z (hZEF hz).1 e he), fun y hy => ?_⟩
  have hyE : y ∈ E := (by rw [← hF.sup_sec2Z]; exact hy : y ∈ E ⊓ F).1
  have h1 : y⁻¹ * e⁻¹ * y * e = 1 := by
    calc y⁻¹ * e⁻¹ * y * e = y⁻¹ * e⁻¹ * (y * e) := by group
      _ = y⁻¹ * e⁻¹ * (e * y) := by rw [hcomm y hyE e he]
      _ = 1 := by group
  rw [h1]
  exact (sec2Z A E F).one_mem

theorem mem_centralizerMod_of_rightConjugate_le
    (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) {p : G}
    (hp : p ∈ sec2P E) (hpEF : rightConjugate R p ≤ E ⊓ F) :
    p ∈ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hPR := sec2P_inf_normalizer_eq hD hT hCE (isPGroup_two_of_isElemAbelian hF.elemE)
  have hKte := AS76b.tightlyEmbedded_centralizer hF.base.hyp.standard
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hZ := hF.sec2Z_eq
  have hRZ := hF.sup_sec2Z
  have hpN := Sec2.sec2P_le E hp
  by_cases hQR : rightConjugate R p = R
  · exact le_centralizerMod hF (hPR.le ⟨hp, (rightConjugate_eq_self_iff R p).mp hQR⟩)
  have hQpt : rightConjugate R p ∈ pointsIn R E := rightConjugate_mem_pointsIn hD.self_mem hpN
  have hsup : R ⊔ rightConjugate R p = E ⊓ F := by
    have h1 := card_sup_of_mem_pointsIn hKte hF.sylowR hD.comm hD.self_mem hQpt (Ne.symm hQR)
    have h2 := hF.card_inf
    rw [hF.cardR] at h1
    exact eq_of_le_of_card_ge (sup_le hREF hpEF) (by omega)
  have hppR : p * p ∈ normalizer (R : Set G) :=
    (hPR.ge (hD.sq_mem_and_commutator_mem hT hCE hp hp).1).2
  have hpEF' : p ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) := by
    rw [← rightConjugate_eq_self_iff, ← hsup, rightConjugate_sup', rightConjugate_mul,
      (rightConjugate_eq_self_iff R (p * p)).mpr hppR, sup_comm]
  have hpEA := hD.normalizer_le_normalizer hpN
  refine mem_centralizerMod.mpr ⟨hp, Sec2.mem_normalizer_of_forall_conj_mem fun z hz => ?_,
    fun y hy => ?_⟩
  · rw [hZ] at hz ⊢
    exact ⟨(mem_normalizer_iff.mp hpEF' z).mp hz.1,
      ((mem_normalizer_iff.mp hpEA z).mp ⟨hz.1.1, hz.2⟩).2⟩
  · have hy' : y ∈ E ⊓ F := by rw [← hRZ]; exact hy
    rw [hZ]
    refine ⟨?_, (hD.commutator_mem hT hCE hF.elemE hy'.1 hp).2⟩
    have := (E ⊓ F).mul_mem ((E ⊓ F).inv_mem hy')
      ((mem_normalizer_iff.mp (inv_mem hpEF') y).mp hy')
    simpa [mul_assoc] using this

theorem centralizerMod_facts
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    E ≤ centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) ∧
      E.relIndex (centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)) = 4 ∧
      centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F) ≤
        normalizer ((E ⊓ F : Subgroup G) : Set G) := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hRZ := hF.sup_sec2Z
  set C := centralizerMod (sec2P E) (R ⊔ sec2Z A E F) (sec2Z A E F)
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hCN : C ≤ normalizer (E : Set G) := hCP.trans (Sec2.sec2P_le E)
  have hCEF : C ≤ normalizer ((E ⊓ F : Subgroup G) : Set G) := fun c hc =>
    hRZ ▸ Sec2.mem_normalizer_of_mem_centralizerMod le_sup_right hc
  refine ⟨le_centralizerMod hF, ?_, hCEF⟩
  have hidx := hT.relIndex_eq_card hD hCN
    (fun x hx h1 => by
      obtain ⟨n, hn⟩ := Sec2.isPGroup_sec2P E ⟨(x : G), hCP hx⟩
      exact hD.mem_of_pointsAction_eq_one hCE h1 (n := n) (by simpa using congrArg Subtype.val hn))
    (fun x hx => hT.pointsAction_mem hD.R_le (hCP hx))
    {Q : ↥(pointsIn R E) | (Q : Subgroup G) ≤ E ⊓ F}
    (fun x hx => by
      rw [Set.mem_ofPred_eq, coe_pointsAction_apply]
      show rightConjugate R (x : G)⁻¹ ≤ E ⊓ F
      have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hREF (x : G)⁻¹
      rwa [(rightConjugate_eq_self_iff _ _).mpr (inv_mem (hCEF hx))] at h)
    (fun Q hQ => by
      obtain ⟨p, hp, hpQ⟩ := htr Q Q.2
      have hpN := Sec2.sec2P_le E hp
      refine ⟨⟨p⁻¹, inv_mem hpN⟩, C.inv_mem (mem_centralizerMod_of_rightConjugate_le h11 hE16 hF
        hL hodd hp (by rw [hpQ]; exact hQ)), Subtype.ext ?_⟩
      rw [coe_pointsAction_apply]
      show rightConjugate R p⁻¹⁻¹ = (Q : Subgroup G)
      rw [inv_inv, hpQ])
  rw [hidx, card_points_le_inf h11 hE16 hF hL hodd]

theorem isElemQuot_sec2P
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) : IsElemQuot (sec2P E) E 16 := by
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hE2 : IsPGroup 2 E := isPGroup_two_of_isElemAbelian hF.elemE
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  refine ⟨Sec2.le_sec2P hE2 le_normalizer le_rfl, ?_,
    fun a ha b hb => hD.sq_mem_and_commutator_mem hT hCE ha hb⟩
  have hidx := hT.relIndex_eq_card hD (Sec2.sec2P_le E)
    (fun x hx h1 => by
      obtain ⟨n, hn⟩ := Sec2.isPGroup_sec2P E ⟨(x : G), hx⟩
      exact hD.mem_of_pointsAction_eq_one hCE h1 (n := n) (by simpa using congrArg Subtype.val hn))
    (fun x hx => hT.pointsAction_mem hD.R_le hx) Set.univ (fun _ _ => Set.mem_univ _)
    (fun Q _ => by
      obtain ⟨p, hp, hpQ⟩ := htr Q Q.2
      refine ⟨⟨p⁻¹, inv_mem (Sec2.sec2P_le E hp)⟩, inv_mem hp, Subtype.ext ?_⟩
      rw [coe_pointsAction_apply]
      show rightConjugate R p⁻¹⁻¹ = (Q : Subgroup G)
      rw [inv_inv, hpQ])
  rw [hidx, Nat.card_univ, hT.card_points]

theorem isElemQuot_sec2S
    (h11 : Step11) {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true)
    (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A))
    (hodd : Odd (Nat.card (center ↥A))) :
    IsElemQuot (sec2S A R E F ⊓ sec2P E) E 4 ∧ IsElemQuot (sec2S A R E F) E 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hE2 : IsPGroup 2 E := isPGroup_two_of_isElemAbelian hF.elemE
  have hPR := sec2P_inf_normalizer_eq hD hT hCE hE2
  obtain ⟨hEC, hCidx, hCEF⟩ := centralizerMod_facts h11 hE16 hF hL hodd
  have hZ := hF.sec2Z_eq
  have hRZ := hF.sup_sec2Z
  have hFN := hF.F_le_normalizer hL hodd
  set Z := sec2Z A E F
  set C := centralizerMod (sec2P E) (R ⊔ Z) Z
  have hSdef : sec2S A R E F = F ⊔ C := rfl
  have hEP : E ≤ sec2P E := Sec2.le_sec2P hE2 le_normalizer le_rfl
  have hREF : R ≤ E ⊓ F := hF.inf_eq ▸ le_sup_left
  have hFcomm : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hZF : Z ≤ F := by rw [hZ]; exact inf_le_left.trans inf_le_right
  have hFR : F ≤ normalizer (R : Set G) := fun f hf => centralizer_le_normalizer _
    (mem_centralizer_iff.mpr fun r hr => hFcomm r (hF.R_le_F hr) f hf)
  have hCP : C ≤ sec2P E := fun c hc => (mem_centralizerMod.mp hc).1
  have hCN : C ≤ normalizer (E : Set G) := hCP.trans (Sec2.sec2P_le E)
  have hF2 : IsPGroup 2 F := isPGroup_two_of_isElemAbelian hF.elemF
  have hFC : F ≤ normalizer (C : Set G) := by
    intro f hf
    have hfZ : f ∈ normalizer (Z : Set G) := centralizer_le_normalizer _
      (mem_centralizer_iff.mpr fun z hz => (hFcomm f hf z (hZF hz)).symm)
    refine Sec2.mem_normalizer_of_forall_conj_mem fun c hc => ?_
    obtain ⟨hcP, hcZ, hcc⟩ := mem_centralizerMod.mp hc
    refine mem_centralizerMod.mpr ⟨(mem_normalizer_iff.mp
      (Sec2.normalizer_le_normalizer_sec2P E (hFN hf)) c).mp hcP,
      mul_mem (mul_mem hfZ hcZ) (inv_mem hfZ), fun y hy => ?_⟩
    have hyF : y ∈ F := (by rw [← hRZ]; exact hy : y ∈ E ⊓ F).2
    have hfy : f⁻¹ * y * f = y := by rw [mul_assoc, ← hFcomm f hf y hyF, inv_mul_cancel_left]
    have hw := hcc y hy
    have heq : y⁻¹ * (f * c * f⁻¹)⁻¹ * y * (f * c * f⁻¹) = y⁻¹ * c⁻¹ * y * c := by
      calc y⁻¹ * (f * c * f⁻¹)⁻¹ * y * (f * c * f⁻¹)
          = f * ((f⁻¹ * y * f)⁻¹ * c⁻¹ * (f⁻¹ * y * f) * c) * f⁻¹ := by group
        _ = f * (y⁻¹ * c⁻¹ * y * c) * f⁻¹ := by rw [hfy]
        _ = y⁻¹ * c⁻¹ * y * c := by rw [hFcomm f hf _ (hZF hw), mul_inv_cancel_right]
    rw [heq]
    exact hw
  have hFC' : ((F ⊔ C : Subgroup G) : Set G) = (F : Set G) * C :=
    coe_mul_of_left_le_normalizer_right F C hFC
  have hSP : sec2S A R E F ⊓ sec2P E = C := by
    rw [hSdef]
    refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hCP)
    have hx' : x ∈ ((F ⊔ C : Subgroup G) : Set G) := hx.1
    rw [hFC'] at hx'
    obtain ⟨f, hf, c, hc, rfl⟩ := hx'
    have hfP : f ∈ sec2P E := by
      have := (sec2P E).mul_mem hx.2 ((sec2P E).inv_mem (hCP hc))
      simpa using this
    exact C.mul_mem (hEC (hPR.le ⟨hfP, hFR hf⟩)) hc
  have hCcard : Nat.card C = 4 * 64 := by
    have h := relIndex_mul_card E C
    rw [inf_eq_left.mpr hEC, hCidx, hF.cardE] at h
    exact h.symm
  have hCF : C ⊓ F = E ⊓ F := le_antisymm (fun x hx => ⟨hPR.le ⟨hCP hx.1, hFR hx.2⟩, hx.2⟩)
    (inf_le_inf_right F hEC)
  have hScard : Nat.card (sec2S A R E F) = 16 * 64 := by
    have h := card_sup_mul_card_inf (H := C) (R := F) hFC
    rw [hCF, hF.card_inf, hCcard, hF.cardF, sup_comm] at h
    rw [hSdef]
    omega
  have hES : E ≤ sec2S A R E F := by
    rw [hSdef]
    exact hEC.trans le_sup_right
  have hSidx : E.relIndex (sec2S A R E F) = 16 := by
    have h := relIndex_mul_card E (sec2S A R E F)
    rw [inf_eq_left.mpr hES, hScard, hF.cardE] at h
    omega
  have hS2 : IsPGroup 2 (F ⊔ C : Subgroup G) :=
    hF2.to_sup_of_normal_right' ((Sec2.isPGroup_sec2P E).to_le hCP) hFC
  have hfix : ∀ f : ↥(normalizer (E : Set G)), (f : G) ∈ F → ∀ Q : ↥(pointsIn R E),
      (Q : Subgroup G) ≤ E ⊓ F → pointsAction R E f Q = Q := by
    intro f hf Q hQ
    apply Subtype.ext
    rw [coe_pointsAction_apply, rightConjugate_eq_self_iff]
    exact inv_mem (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun q hq =>
      hFcomm q (hQ hq).2 f hf))
  have hmaps : ∀ c : ↥(normalizer (E : Set G)), (c : G) ∈ C →
      ((pointsAction R E c ⟨R, hD.self_mem⟩ : ↥(pointsIn R E)) : Subgroup G) ≤ E ⊓ F := by
    intro c hc
    rw [coe_pointsAction_apply]
    show rightConjugate R (c : G)⁻¹ ≤ E ⊓ F
    have h := AschbacherTheorem3.rightConjugate_le_rightConjugate hREF (c : G)⁻¹
    rwa [(rightConjugate_eq_self_iff _ _).mpr (inv_mem (hCEF hc))] at h
  have hcomm : ∀ f c : ↥(normalizer (E : Set G)), (f : G) ∈ F → (c : G) ∈ C →
      Commute (pointsAction R E f) (pointsAction R E c) := by
    intro f c hf hc
    have htT : pointsAction R E c ∈ T := hT.pointsAction_mem hD.R_le (hCP hc)
    have hsts : pointsAction R E f * pointsAction R E c * (pointsAction R E f)⁻¹ ∈ T :=
      (mem_normalizer_iff.mp (hT.range_le ⟨f, rfl⟩) _).mp htT
    have hsinv : (pointsAction R E f)⁻¹ ⟨R, hD.self_mem⟩ = ⟨R, hD.self_mem⟩ := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hfix f hf _ hREF).symm
    have h1 : ((pointsAction R E c)⁻¹ * (pointsAction R E f * pointsAction R E c *
        (pointsAction R E f)⁻¹)) ⟨R, hD.self_mem⟩ = ⟨R, hD.self_mem⟩ := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsinv,
        hfix f hf _ (hmaps c hc), Equiv.Perm.inv_eq_iff_eq]
    have h2 := hT.eq_one_of_apply_eq (T.mul_mem (T.inv_mem htT) hsts) h1
    rw [inv_mul_eq_one] at h2
    show pointsAction R E f * pointsAction R E c = pointsAction R E c * pointsAction R E f
    calc pointsAction R E f * pointsAction R E c
        = pointsAction R E f * pointsAction R E c * (pointsAction R E f)⁻¹ *
          pointsAction R E f := by group
      _ = pointsAction R E c * pointsAction R E f := by rw [← h2]
  have hdecomp : ∀ a ∈ F ⊔ C, ∃ f c : ↥(normalizer (E : Set G)), (f : G) ∈ F ∧ (c : G) ∈ C ∧
      a = f * c := by
    intro a ha
    have ha' : a ∈ ((F ⊔ C : Subgroup G) : Set G) := ha
    rw [hFC'] at ha'
    obtain ⟨f, hf, c, hc, rfl⟩ := ha'
    exact ⟨⟨f, hFN hf⟩, ⟨c, hCN hc⟩, hf, hc, rfl⟩
  have hkerS : ∀ x : ↥(normalizer (E : Set G)), (x : G) ∈ F ⊔ C → pointsAction R E x = 1 →
      (x : G) ∈ E := fun x hx h1 => by
    obtain ⟨n, hn⟩ := hS2 ⟨(x : G), hx⟩
    exact hD.mem_of_pointsAction_eq_one hCE h1 (n := n) (by simpa using congrArg Subtype.val hn)
  have hsqF : ∀ f : ↥(normalizer (E : Set G)), (f : G) ∈ F →
      pointsAction R E f * pointsAction R E f = 1 := by
    intro f hf
    rw [← map_mul]
    have : f * f = 1 := Subtype.ext (by rw [coe_mul, coe_one, ← sq]; exact hF.elemF.2 _ hf)
    rw [this, map_one]
  have hsqC : ∀ c : ↥(normalizer (E : Set G)), (c : G) ∈ C →
      pointsAction R E c * pointsAction R E c = 1 := by
    intro c hc
    rw [← sq]
    exact hT.elem.2 _ (hT.pointsAction_mem hD.R_le (hCP hc))
  have hSsq : ∀ a ∈ sec2S A R E F, ∀ b ∈ sec2S A R E F, a * a ∈ E ∧ a * b * a⁻¹ * b⁻¹ ∈ E := by
    intro a ha b hb
    rw [hSdef] at ha hb
    obtain ⟨f₁, c₁, hf₁, hc₁, rfl⟩ := hdecomp a ha
    obtain ⟨f₂, c₂, hf₂, hc₂, rfl⟩ := hdecomp b hb
    have hff : Commute (pointsAction R E f₁) (pointsAction R E f₂) := by
      show pointsAction R E f₁ * pointsAction R E f₂ = pointsAction R E f₂ * pointsAction R E f₁
      rw [← map_mul, ← map_mul, show f₁ * f₂ = f₂ * f₁ from Subtype.ext (hFcomm _ hf₁ _ hf₂)]
    have hcc : Commute (pointsAction R E c₁) (pointsAction R E c₂) :=
      congrArg Subtype.val (hT.elem.1.is_comm.comm
        ⟨_, hT.pointsAction_mem hD.R_le (hCP hc₁)⟩ ⟨_, hT.pointsAction_mem hD.R_le (hCP hc₂)⟩)
    obtain ⟨h1, h2⟩ := Sec2.mul_mul_eq_one_and_commutator_eq_one (hsqF f₁ hf₁) (hsqC c₁ hc₁)
      (hcomm f₁ c₁ hf₁ hc₁) (hcomm f₁ c₂ hf₁ hc₂) (hcomm f₂ c₁ hf₂ hc₁) hff hcc
    have hm₁ : ((f₁ * c₁ : ↥(normalizer (E : Set G))) : G) ∈ F ⊔ C :=
      (F ⊔ C).mul_mem (mem_sup_left hf₁) (mem_sup_right hc₁)
    have hm₂ : ((f₂ * c₂ : ↥(normalizer (E : Set G))) : G) ∈ F ⊔ C :=
      (F ⊔ C).mul_mem (mem_sup_left hf₂) (mem_sup_right hc₂)
    refine ⟨hkerS ((f₁ * c₁) * (f₁ * c₁)) ((F ⊔ C).mul_mem hm₁ hm₁) ?_,
      hkerS ((f₁ * c₁) * (f₂ * c₂) * (f₁ * c₁)⁻¹ * (f₂ * c₂)⁻¹)
        ((F ⊔ C).mul_mem ((F ⊔ C).mul_mem ((F ⊔ C).mul_mem hm₁ hm₂) ((F ⊔ C).inv_mem hm₁))
          ((F ⊔ C).inv_mem hm₂)) ?_⟩
    · rw [map_mul, map_mul]
      exact h1
    · simp only [map_mul, map_inv]
      exact h2
  exact ⟨⟨le_inf hES hEP, by rw [hSP]; exact hCidx, fun a ha b hb =>
    hD.sq_mem_and_commutator_mem hT hCE ha.2 hb.2⟩, ⟨hES, hSidx, hSsq⟩⟩

end Frame

theorem step21_of (h11 : Step11)
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) : Step21 := by
  intro G _ _ A R g E F hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF := hS.frame
  have hL := hS.type
  have hodd := hS.odd
  obtain ⟨hD, T, hT⟩ := exists_pointsData h11 hE16 hF hL hodd
  have hCE := mem_of_mem_centralizer_of_frame hF hL hodd
  have hE2 : IsPGroup 2 E := isPGroup_two_of_isElemAbelian hF.elemE
  have htr := exists_mem_sec2P_rightConjugate_eq h11 hE16 hF hL hodd
  have hPq := isElemQuot_sec2P h11 hE16 hF hL hodd
  obtain ⟨hCEO, hCcard, -⟩ := centralizer_eq_sup_oddCoreIn hF hL hodd
  have hFN := hF.F_le_normalizer hL hodd
  set P := sec2P E
  set O := AS76b.oddCoreIn (centralizer (E : Set G))
  have hPN : P ≤ normalizer (E : Set G) := Sec2.sec2P_le E
  have hNP : normalizer (E : Set G) ≤ normalizer (P : Set G) :=
    Sec2.normalizer_le_normalizer_sec2P E
  have hP2 : IsPGroup 2 P := Sec2.isPGroup_sec2P E
  have hEP : E ≤ P := hPq.1
  have hOC : O ≤ centralizer (E : Set G) := AS76b.oddCoreIn_le _
  have hON : O ≤ normalizer (E : Set G) := hOC.trans (centralizer_le_normalizer _)
  have hNO : normalizer (E : Set G) ≤ normalizer (O : Set G) := fun n hn =>
    AS76b.normalizer_le_normalizer_oddCoreIn _ (normalizer_le_normalizer_centralizer E hn)
  have hOP : O ⊓ P = ⊥ := AS76b.oddCoreIn_inf_eq_bot hP2
  have hPcard : Nat.card P = 16 * 64 := by
    have h := relIndex_mul_card E P
    rw [inf_eq_left.mpr hEP, hPq.2.1, hF.cardE] at h
    exact h.symm
  have c1 : (P ⊔ F) ⊓ centralizer (E : Set G) = E := by
    have hPF2 : IsPGroup 2 (P ⊔ F : Subgroup G) :=
      hP2.to_sup_of_normal_left' (isPGroup_two_of_isElemAbelian hF.elemF) (hFN.trans hNP)
    refine le_antisymm (fun x hx => ?_) (le_inf (hEP.trans le_sup_left)
      fun e he => mem_centralizer_iff.mpr fun e' he' => hD.comm e' he' e he)
    obtain ⟨n, hn⟩ := hPF2 ⟨x, hx.1⟩
    exact hCE x hx.2 n (by simpa using congrArg Subtype.val hn)
  have c3 : O ≤ centralizer (P : Set G) := by
    intro o ho
    rw [mem_centralizer_iff]
    intro p hp
    have h1 : o * p * o⁻¹ * p⁻¹ ∈ P :=
      P.mul_mem ((mem_normalizer_iff.mp (hNP (hON ho)) p).mp hp) (P.inv_mem hp)
    have h2 : o * p * o⁻¹ * p⁻¹ ∈ O := by
      have := O.mul_mem ho ((mem_normalizer_iff.mp (hNO (hPN hp)) o⁻¹).mp (O.inv_mem ho))
      simpa [mul_assoc] using this
    have h3 : o * p * o⁻¹ * p⁻¹ = 1 := by
      have h4 : o * p * o⁻¹ * p⁻¹ ∈ O ⊓ P := ⟨h2, h1⟩
      rwa [hOP, mem_bot] at h4
    exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h3)).symm
  have c7 : normalizer (E : Set G) = P ⊔ O ⊔ (normalizer (E : Set G) ⊓ normalizer (R : Set G)) := by
    refine le_antisymm (fun n hn => ?_) (sup_le (sup_le hPN hON) inf_le_left)
    obtain ⟨p, hp, hpQ⟩ := htr (rightConjugate R n⁻¹)
      (rightConjugate_mem_pointsIn hD.self_mem (inv_mem hn))
    have hpn : p * n ∈ normalizer (R : Set G) := by
      rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, hpQ, rightConjugate_mul,
        inv_mul_cancel, rightConjugate_one]
    rw [show n = p⁻¹ * (p * n) by group]
    exact mul_mem (mem_sup_left (mem_sup_left (P.inv_mem hp)))
      (mem_sup_right ⟨mul_mem (hPN hp) hn, hpn⟩)
  have c8 : ((P ⊔ O) ⊓ centralizer (E : Set G)).relIndex (P ⊔ O) = 16 := by
    have hPO : Nat.card (P ⊔ O : Subgroup G) = Nat.card P * Nat.card O :=
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P O
        (hON.trans hNP) (disjoint_iff.mpr (by rw [inf_comm]; exact hOP))
    have hCPO : centralizer (E : Set G) ≤ P ⊔ O := by
      rw [hCEO]
      exact sup_le_sup_right hEP O
    rw [inf_relIndex_left]
    have h1 := relIndex_mul_card (centralizer (E : Set G)) (P ⊔ O)
    rw [inf_eq_left.mpr hCPO, hCcard, hPO, hPcard] at h1
    have hO0 : 0 < Nat.card O := Nat.card_pos
    have h2 := Nat.eq_of_mul_eq_mul_right hO0
      (show (centralizer (E : Set G)).relIndex (P ⊔ O) * 64 * Nat.card O = 16 * 64 * Nat.card O by
        rw [← h1]; ring)
    omega
  obtain ⟨hSP, hS⟩ := isElemQuot_sec2S h11 hE16 hF hL hodd
  exact ⟨c1, hPq, c3, by rw [inf_comm]; exact hOP, sup_le hPN hON,
    fun n hn => mem_normalizer_sup (hNP hn) (hNO hn), c7, c8, hSP, hS⟩

end CFSG.ComponentClassification.AS81
