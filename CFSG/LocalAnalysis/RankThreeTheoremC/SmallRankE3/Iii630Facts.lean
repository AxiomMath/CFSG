module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Iii630Group2
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wDerive
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wExists
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wPlaneRank
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62wSylowX
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yLemma629
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def KFactHallHigmanOdd : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (F V : Subgroup K) (z : K) (f r : ℕ),
    f.Prime → r.Prime → r ≠ f → 5 ≤ r → IsElemAbelian f F → IsPGroup r V →
    V ≤ normalizer (F : Set K) → z ∈ normalizer (F : Set K) → z ^ 3 = 1 →
    z ∈ normalizer (V : Set K) → (∀ a ∈ F, z * a * z⁻¹ = a → a = 1) →
    ∀ v ∈ V, z * v * z⁻¹ * v⁻¹ ∈ centralizer (F : Set K)

@[expose] def KFactOutQ8Quaternion : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (S S₀ R : Subgroup K) (n : ℕ),
    smallRankIsQ8Quaternion S n → S₀ ≤ S → (S₀.subgroupOf S).Normal → R ≤ S₀ →
    Nonempty (↥R ≃* QuaternionGroup 2) →
    ∀ g ∈ normalizer (S₀ : Set K), Nat.Coprime (orderOf g) 6 → g ∈ centralizer (S₀ : Set K)

structure Facts630 (G : Type) [Group G] [Finite G] (M : Subgroup G) (x z : G) (f : ℕ) : Prop where
  prime : f.Prime
  five_le : 5 ≤ f
  elem : IsElemAbelian f (smallRankF 3 f x)
  card : Nat.card (smallRankF 3 f x) = f ^ 4
  ne_bot : smallRankF 3 f x ≠ ⊥
  inf_M : smallRankF 3 f x ⊓ M = ⊥
  x_ne : x ≠ 1
  x_three : x ^ 3 = 1
  z_three : z ^ 3 = 1
  xz : x * z = z * x
  x_M : x ∈ M
  B_le_M : zpowers x ⊔ zpowers z ≤ M
  Cz_le_M : centralizer ({z} : Set G) ≤ M
  F_le_Cx : smallRankF 3 f x ≤ centralizer ({x} : Set G)
  Cx_le_N : centralizer ({x} : Set G) ≤ normalizer (smallRankF 3 f x : Set G)
  x_C : x ∈ centralizer (smallRankF 3 f x : Set G)
  z_N : z ∈ normalizer (smallRankF 3 f x : Set G)
  z_not_C : z ∉ centralizer (smallRankF 3 f x : Set G)
  C_odd : ¬ 2 ∣ Nat.card (centralizer (smallRankF 3 f x : Set G))
  x_sylow : IsSylowOf 3 (zpowers x) (centralizer (smallRankF 3 f x : Set G))
  z_fpf : ∀ a ∈ smallRankF 3 f x, z * a * z⁻¹ = a → a = 1

section R10C1

open CFSG.Open CFSG.ABGLocalTools CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem facts630 (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    {f : ℕ} (hyp : Lemma630Hyp G 3 P M x z T f) : Facts630 G M x z f := by
  obtain ⟨hf, -, h28, hfp, hf2, hfD, h29⟩ := hyp
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Fact f.Prime := ⟨hfp⟩
  have hf3 : f ≠ 3 := sr629_ne_prime hp hfp x hfD
  have hfive : 5 ≤ f := sr629_five_le hfp hf2 hf3
  obtain ⟨-, -, hlr, hFe, hF4, -⟩ := h29
  obtain ⟨-, -, -, hfit⟩ := h28
  have hFne : smallRankF 3 f x ≠ ⊥ := by
    intro hF
    have h1 : Nat.card (smallRankF 3 f x) = 1 := by rw [hF]; exact Subgroup.card_bot
    rw [hF4] at h1
    exact (Nat.one_lt_pow (by norm_num) hfp.one_lt).ne' h1
  have hFM : smallRankF 3 f x ⊓ M = ⊥ := by
    rw [eq_bot_iff, ← hfit]
    exact inf_le_inf_right M (sr629_F_le_fitting hp hfp hf2 x)
  have hFD : smallRankF 3 f x ≤ smallRankD 3 x :=
    (sr629_omega_center_le f _).trans (CFSG.LieType.BorelTits.pCoreOf_le f _)
  have hDC : smallRankD 3 x ≤ centralizer ({x} : Set G) := sSup_le fun _ hK => hK.1
  have hxCF : x ∈ centralizer (smallRankF 3 f x : Set G) :=
    mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hDC (hFD ha))
  have hzx : z ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem).symm
  have hCN : ∀ g ∈ centralizer ({x} : Set G),
      g ∈ normalizer (centralizer (smallRankF 3 f x : Set G) : Set G) := fun g hg =>
    sr630c_mem_normalizer_centralizer (sr629_centralizer_le_normalizer_F (f := f) hp x hg)
  have hCzM : centralizer ({z} : Set G) ≤ M :=
    (sr628_centralizer_le_normalizer_zpowers z).trans (hf.normalizer_zpowers_le hS)
  have hzCF : z ∉ centralizer (smallRankF 3 f x : Set G) := by
    intro hz
    apply hFne
    rw [eq_bot_iff, ← hFM]
    refine fun a ha => ⟨ha, hCzM ?_⟩
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz a ha)
  have hpl : SmallRankPlane 3 (P : Subgroup G) x z :=
    SmallRankPlane.of_situation hS hf.situation hf.point hf.central
  have hPx : IsSylowOf 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) :=
    isSylowOf_iff.mpr ⟨inf_le_right, P.isPGroup'.to_inf_left, hf.point.sylow_centralizer⟩
  have hrank : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hf.situation.largeObstruction_empty x ⟨hf.sylow_le hS hf.point.mem, hf.point.ne_one,
      hf.point.pow_eq_one, by omega, hf.point.not_centralizer_le⟩
  have hCx : ∀ E : Subgroup G, E ≤ centralizer ({x} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 2 := by
    intro E hE hEe
    have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk2 := CFSG.SectionRank.le_pRank hp.one_lt hE hEe hk
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos (by omega)
  have hA3 : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian 3 A ∧
      Nat.card A = 3 ^ 3 := by
    obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hf.situation.mem_sigmaA
      hf.situation.isCoreMaxLocal
    obtain ⟨A, hAP, hAe, hAc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (P : Subgroup G)
    rw [hP3] at hAc
    exact ⟨A, hAP, hAe, hAc⟩
  have hsyl : IsSylowOf 3 (zpowers x) (centralizer (smallRankF 3 f x : Set G)) :=
    sr630e_zpowers_isSylowOf hp (by norm_num) hpl hf.central.centralizes hf.point.ne_one
      hf.point.pow_eq_one hPx hCx hA3 hxCF hzCF (hCN z hzx)
  have hodd := sr630e_not_two_dvd_card_centralizer hfp hFe hF4 hlr
  refine ⟨hfp, hfive, hFe, hF4, hFne, hFM, hf.point.ne_one, hf.point.pow_eq_one,
    hf.central.pow_eq_one, mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem,
    hf.sylow_le hS hf.point.mem, hf.B_le_M hS, hCzM, hFD.trans hDC, ?_, hxCF, ?_, hzCF, hodd,
    hsyl, ?_⟩
  · intro g hg
    exact sr629_centralizer_le_normalizer_F (f := f) hp x hg
  · exact sr629_centralizer_le_normalizer_F (f := f) hp x hzx
  · intro a ha hza
    have hCa : a ∈ centralizer ({z} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hza).symm
    have haFM : a ∈ smallRankF 3 f x ⊓ M := ⟨ha, hCzM hCa⟩
    rw [hFM] at haFM
    exact Subgroup.mem_bot.mp haFM

end R10C1

section R10C2

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a22_q8_central :
    ∀ q : QuaternionGroup 2, (∀ r : QuaternionGroup 2, r * q = q * r) →
      q = 1 ∨ q = QuaternionGroup.a 2 := by
  decide

private theorem r10a22_q8_a2_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide

private theorem r10a22_q8_a2_central :
    ∀ r : QuaternionGroup 2, r * QuaternionGroup.a 2 = QuaternionGroup.a 2 * r := by
  decide

private theorem r10a22_center_unique (R : Subgroup G) (e : ↥R ≃* QuaternionGroup 2) :
    ∃ y : G, y ∈ smallRankCenter R ∧ y ≠ 1 ∧ ∀ w ∈ smallRankCenter R, w ≠ 1 → w = y := by
  obtain ⟨u, hu⟩ : ∃ u : ↥R, u = e.symm (QuaternionGroup.a 2) := ⟨_, rfl⟩
  have hcomm : ∀ k : ↥R, k * u = u * k := by
    intro k
    apply e.injective
    rw [map_mul, map_mul, hu, MulEquiv.apply_symm_apply]
    exact r10a22_q8_a2_central (e k)
  have hu1 : u ≠ 1 := by
    intro h
    apply r10a22_q8_a2_ne_one
    rw [← MulEquiv.apply_symm_apply e (QuaternionGroup.a 2), ← hu, h, map_one]
  refine ⟨(u : G), ⟨u.2, mem_centralizer_iff.mpr fun h hh => ?_⟩,
    fun h => hu1 (Subtype.ext h), ?_⟩
  · exact congrArg Subtype.val (hcomm ⟨h, hh⟩)
  · rintro w ⟨hwR, hwC⟩ hw1
    obtain ⟨k, rfl⟩ : ∃ k : ↥R, (k : G) = w := ⟨⟨w, hwR⟩, rfl⟩
    have hkcomm : ∀ s : ↥R, s * k = k * s := by
      intro s
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact mem_centralizer_iff.mp hwC _ s.2
    have hec : ∀ r : QuaternionGroup 2, r * e k = e k * r := by
      intro r
      obtain ⟨s, rfl⟩ := e.surjective r
      rw [← map_mul, ← map_mul, hkcomm s]
    rcases r10a22_q8_central (e k) hec with h | h
    · exfalso
      apply hw1
      rw [show k = 1 from e.injective (h.trans (map_one e).symm), Subgroup.coe_one]
    · have hk : k = u := by
        rw [hu, ← h, MulEquiv.symm_apply_apply]
      exact congrArg Subtype.val hk

private theorem r10a22_R_le_S (x z : G) (T : Subgroup G)
    (hzN : ∀ g ∈ zpowers z, g ∈ normalizer (smallRankS x T : Set G)) :
    smallRankR x z T ≤ smallRankS x T := by
  show ⁅zpowers z, smallRankS x T⁆ ≤ smallRankS x T
  rw [Subgroup.commutator_le]
  intro g hg s hs
  rw [commutatorElement_def]
  exact mul_mem ((mem_normalizer_iff.mp (hzN g hg) s).mp hs) (inv_mem hs)

private theorem r10a22_zpowers_conj (z g a : G) (hg : g ∈ zpowers z) (ha : a ∈ zpowers z) :
    g * a * g⁻¹ = a := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have hc : Commute (z ^ m) (z ^ k) := ((Commute.refl z).zpow_right k).zpow_left m
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]

private theorem r10a22_conj_zpowers (z g a : G) (hg : g ∈ zpowers z) (ha : a ∈ zpowers z) :
    g * a * g⁻¹ ∈ zpowers z := by
  rw [r10a22_zpowers_conj z g a hg ha]
  exact ha

private theorem r10a22_conj_R (x z : G) (T : Subgroup G) (g : G)
    (hS' : ∀ s ∈ smallRankS x T, g * s * g⁻¹ ∈ smallRankS x T)
    (hZ : ∀ a ∈ zpowers z, g * a * g⁻¹ ∈ zpowers z) :
    ∀ r ∈ smallRankR x z T, g * r * g⁻¹ ∈ smallRankR x z T := by
  have hle : (smallRankR x z T).map (MulAut.conj g).toMonoidHom ≤ smallRankR x z T := by
    show (⁅zpowers z, smallRankS x T⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤
      ⁅zpowers z, smallRankS x T⁆
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hZ a ha
    · rintro _ ⟨s, hs, rfl⟩
      exact hS' s hs
  intro r hr
  exact hle (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hr)

theorem exists_y630 (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    {f : ℕ} (hyp : Lemma630Hyp G 3 P M x z T f) :
    ∃ y : G, y ∈ smallRankS x T ∧ y ≠ 1 ∧ y * y = 1 ∧ z * y = y * z ∧ x * y = y * x ∧
      ∀ a ∈ smallRankF 3 f x, y * a * y⁻¹ = a⁻¹ := by
  obtain ⟨hf, -, h28, -, -, -, h29⟩ := hyp
  obtain ⟨e⟩ := h28.2.1 rfl
  obtain ⟨⟨-, -, hcenter⟩, -, -, -, -, hinv⟩ := h29
  have hzN : ∀ g ∈ zpowers z, g ∈ normalizer (smallRankS x T : Set G) :=
    fun g hg => hf.z_le_normalizer_S hg
  obtain ⟨y, hyZ, hy1, hyuniq⟩ := r10a22_center_unique (smallRankR x z T) e
  have hyS : y ∈ smallRankS x T := r10a22_R_le_S x z T hzN hyZ.1
  have hyy : y * y = 1 := by
    have hyΩ : y ∈ smallRankOmega 2 (smallRankCenter (smallRankS x T)) := by
      rw [← hcenter]
      exact hyZ
    rw [← pow_two]
    exact (sr629_isElemAbelian_omega_center 2 (smallRankS x T)).2 y hyΩ
  have hzN_z : z ∈ normalizer (smallRankS x T : Set G) := hzN z (mem_zpowers z)
  have hzR : ∀ r ∈ smallRankR x z T, z * r * z⁻¹ ∈ smallRankR x z T :=
    r10a22_conj_R x z T z (fun s hs => (mem_normalizer_iff.mp hzN_z s).mp hs)
      (fun a ha => r10a22_conj_zpowers z z a (mem_zpowers z) ha)
  have hzR' : ∀ r ∈ smallRankR x z T, z⁻¹ * r * z⁻¹⁻¹ ∈ smallRankR x z T :=
    r10a22_conj_R x z T z⁻¹ (fun s hs => (mem_normalizer_iff.mp (inv_mem hzN_z) s).mp hs)
      (fun a ha => r10a22_conj_zpowers z z⁻¹ a (inv_mem (mem_zpowers z)) ha)
  have hyconj : z * y * z⁻¹ = y := by
    have hmem : z * y * z⁻¹ ∈ smallRankCenter (smallRankR x z T) := by
      refine ⟨hzR y hyZ.1, mem_centralizer_iff.mpr fun r hr => ?_⟩
      have hc : (z⁻¹ * r * z⁻¹⁻¹) * y = y * (z⁻¹ * r * z⁻¹⁻¹) :=
        mem_centralizer_iff.mp hyZ.2 _ (hzR' r hr)
      calc r * (z * y * z⁻¹) = z * ((z⁻¹ * r * z⁻¹⁻¹) * y) * z⁻¹ := by group
        _ = z * (y * (z⁻¹ * r * z⁻¹⁻¹)) * z⁻¹ := by rw [hc]
        _ = z * y * z⁻¹ * r := by group
    have hne : z * y * z⁻¹ ≠ 1 := by
      intro h
      apply hy1
      calc y = z⁻¹ * (z * y * z⁻¹) * z⁻¹⁻¹ := by group
        _ = 1 := by rw [h, mul_one, inv_inv, inv_mul_cancel]
    exact hyuniq _ hmem hne
  have hzy : z * y = y * z := by
    rw [mul_inv_eq_iff_eq_mul] at hyconj
    exact hyconj
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp hyS.2).symm
  exact ⟨y, hyS, hy1, hyy, hzy, hxy, hinv y hyZ hy1⟩

end R10C2

section R10C3

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private def r10a23_map (x y : QuaternionGroup 2) : QuaternionGroup 2 → QuaternionGroup 2
  | .a i => x ^ (ZMod.val i)
  | .xa i => y * x ^ (ZMod.val i)

private theorem r10a23_map_iter_twelve :
    ∀ x y : QuaternionGroup 2,
      (∀ g h : QuaternionGroup 2,
        r10a23_map x y (g * h) = r10a23_map x y g * r10a23_map x y h) →
      (∀ g₁ g₂ : QuaternionGroup 2, r10a23_map x y g₁ = r10a23_map x y g₂ → g₁ = g₂) →
      ∀ g : QuaternionGroup 2, (r10a23_map x y)^[12] g = g := by
  decide +kernel

private theorem r10a23_map_one {f : QuaternionGroup 2 → QuaternionGroup 2}
    (hf : ∀ g h, f (g * h) = f g * f h) : f 1 = 1 := by
  have h : f 1 * f 1 = f 1 * 1 := by rw [mul_one, ← hf, mul_one]
  exact mul_left_cancel h

private theorem r10a23_map_pow {f : QuaternionGroup 2 → QuaternionGroup 2}
    (hf : ∀ g h, f (g * h) = f g * f h) (g : QuaternionGroup 2) (n : ℕ) :
    f (g ^ n) = (f g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, r10a23_map_one hf]
  | succ n ih => rw [pow_succ, pow_succ, hf, ih]

private theorem r10a23_map_eq {f : QuaternionGroup 2 → QuaternionGroup 2}
    (hf : ∀ g h, f (g * h) = f g * f h) (q : QuaternionGroup 2) :
    f q = r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) q := by
  have ha : ∀ i : ZMod (2 * 2),
      f (QuaternionGroup.a i) = (f (QuaternionGroup.a 1)) ^ (ZMod.val i) := by
    intro i
    rw [← r10a23_map_pow hf, QuaternionGroup.a_one_pow, ZMod.natCast_zmod_val]
  cases q with
  | a i => exact (ha i).trans rfl
  | xa i =>
    have hxa : QuaternionGroup.xa i = QuaternionGroup.xa 0 * QuaternionGroup.a i := by
      rw [QuaternionGroup.xa_mul_a, zero_add]
    have hfxa : f (QuaternionGroup.xa i) =
        f (QuaternionGroup.xa 0) * (f (QuaternionGroup.a 1)) ^ (ZMod.val i) := by
      rw [hxa, hf, ha i]
    exact hfxa.trans rfl

private theorem r10a23_iter_three {α : Type} (φ : α → α) (k : ℕ)
    (h12 : φ^[12] = id) (hk : φ^[3 ^ k] = id) : φ^[3] = id := by
  cases k with
  | zero =>
    have hφ : φ = id := by simpa using hk
    rw [hφ, Function.iterate_id]
  | succ j =>
    have hc : Nat.Coprime (3 ^ j) 4 := Nat.Coprime.pow_left j (by norm_num)
    have hg : Nat.gcd (3 ^ (j + 1)) 12 = 3 := by
      rw [show 3 ^ (j + 1) = 3 * 3 ^ j by ring, show (12 : ℕ) = 3 * 4 by norm_num,
        Nat.gcd_mul_left, Nat.Coprime.gcd_eq_one hc, mul_one]
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Function.End α, ψ = φ := ⟨φ, rfl⟩
    have h1 : ψ ^ 12 = 1 := by rw [hψ]; exact h12
    have h2 : ψ ^ (3 ^ (j + 1)) = 1 := by rw [hψ]; exact hk
    have h3 : ψ ^ (Nat.gcd (3 ^ (j + 1)) 12) = 1 := pow_gcd_eq_one.mpr ⟨h2, h1⟩
    rw [hg, hψ] at h3
    exact h3

private def r10a23_conj {K : Type} [Group K] {R : Subgroup K} {g : K}
    (hg : g ∈ normalizer (R : Set K)) (r : R) : R :=
  ⟨g * (r : K) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (r : K)).mp r.2⟩

private theorem r10a23_conj_val {K : Type} [Group K] {R : Subgroup K} {g : K}
    (hg : g ∈ normalizer (R : Set K)) (r : R) :
    ((r10a23_conj hg r : R) : K) = g * (r : K) * g⁻¹ := rfl

private theorem r10a23_conj_iter_val {K : Type} [Group K] {R : Subgroup K} {g : K}
    (hg : g ∈ normalizer (R : Set K)) (n : ℕ) (r : R) :
    (((r10a23_conj hg)^[n] r : R) : K) = g ^ n * (r : K) * (g ^ n)⁻¹ := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', r10a23_conj_val, ih, pow_succ', mul_inv_rev]
    simp only [mul_assoc]

private theorem r10a23_conj_iff {K : Type} [Group K] {R : Subgroup K} {g : K}
    (hg : g ∈ normalizer (R : Set K)) (n : ℕ) :
    g ^ n ∈ centralizer (R : Set K) ↔ ∀ r : R, (r10a23_conj hg)^[n] r = r := by
  constructor
  · intro hc r
    apply Subtype.ext
    rw [r10a23_conj_iter_val]
    have hr := (Subgroup.mem_centralizer_iff.mp hc) (r : K) r.2
    rw [← hr, mul_inv_cancel_right]
  · intro hit
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h' : g ^ n * h * (g ^ n)⁻¹ = h := by
      have := congrArg Subtype.val (hit ⟨h, hh⟩)
      rw [r10a23_conj_iter_val] at this
      exact this
    exact (mul_inv_eq_iff_eq_mul.mp h').symm

theorem pow_three_mem_centralizer_of_q8 {K : Type} [Group K] [Finite K] {R : Subgroup K}
    (hR : Nonempty (↥R ≃* QuaternionGroup 2)) {g : K} (hg : g ∈ normalizer (R : Set K)) {k : ℕ}
    (hk : g ^ (3 ^ k) ∈ centralizer (R : Set K)) : g ^ 3 ∈ centralizer (R : Set K) := by
  obtain ⟨e⟩ := hR
  have hF_mul : ∀ r₁ r₂ : R,
      r10a23_conj hg (r₁ * r₂) = r10a23_conj hg r₁ * r10a23_conj hg r₂ := by
    intro r₁ r₂
    apply Subtype.ext
    simp only [Subgroup.coe_mul, r10a23_conj_val, mul_assoc, inv_mul_cancel_left]
  have hF_inj : ∀ r₁ r₂ : R, r10a23_conj hg r₁ = r10a23_conj hg r₂ → r₁ = r₂ := by
    intro r₁ r₂ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    rw [r10a23_conj_val, r10a23_conj_val] at h'
    simpa using h'
  obtain ⟨f, hfdef⟩ : ∃ f : QuaternionGroup 2 → QuaternionGroup 2,
      ∀ q, f q = e (r10a23_conj hg (e.symm q)) :=
    ⟨fun q => e (r10a23_conj hg (e.symm q)), fun q => rfl⟩
  have hf_mul : ∀ q₁ q₂, f (q₁ * q₂) = f q₁ * f q₂ := by
    intro q₁ q₂
    rw [hfdef, hfdef, hfdef, map_mul e.symm, hF_mul, map_mul e]
  have hf_inj : Function.Injective f := by
    intro q₁ q₂ h
    rw [hfdef, hfdef] at h
    exact e.symm.injective (hF_inj _ _ (e.injective h))
  have hpar : ∀ q, f q = r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) q :=
    fun q => r10a23_map_eq hf_mul q
  have hfeq : f = r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) :=
    funext hpar
  have hhom : ∀ g h : QuaternionGroup 2,
      r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) (g * h) =
        r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) g *
          r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) h := by
    intro g h
    rw [← hpar (g * h), ← hpar g, ← hpar h]
    exact hf_mul g h
  have hinj : ∀ g₁ g₂ : QuaternionGroup 2,
      r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) g₁ =
        r10a23_map (f (QuaternionGroup.a 1)) (f (QuaternionGroup.xa 0)) g₂ → g₁ = g₂ := by
    intro g₁ g₂ h
    rw [← hpar g₁, ← hpar g₂] at h
    exact hf_inj h
  have h12 : f^[12] = id := by
    rw [hfeq]
    exact funext (r10a23_map_iter_twelve (f (QuaternionGroup.a 1))
      (f (QuaternionGroup.xa 0)) hhom hinj)
  have hiter : ∀ (n : ℕ) (r : R), e ((r10a23_conj hg)^[n] r) = f^[n] (e r) := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hfdef]
      simp
  have hfk : f^[3 ^ k] = id := by
    funext q
    have h1 := hiter (3 ^ k) (e.symm q)
    rw [(r10a23_conj_iff hg (3 ^ k)).mp hk (e.symm q)] at h1
    simp only [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hf3 : f^[3] = id := r10a23_iter_three f k h12 hfk
  refine (r10a23_conj_iff hg 3).mpr (fun r => ?_)
  apply e.injective
  have h := hiter 3 r
  rw [hf3] at h
  exact h

end R10C3

section R10C4

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a24_commutator_le_of_normalizes {S : Subgroup G} {z : G}
    (hz : zpowers z ≤ normalizer (S : Set G)) : ⁅zpowers z, S⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro a ha s hs
  have has : a * s * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hz ha) s).mp hs
  rw [commutatorElement_def]
  exact mul_mem has (inv_mem hs)

private theorem r10a24_pow_eq_pow_mod {x : G} (hx3 : x ^ 3 = 1) (m : ℕ) :
    x ^ m = x ^ (m % 3) := by
  conv_lhs => rw [← Nat.div_add_mod m 3]
  rw [pow_add, pow_mul, hx3, one_pow, one_mul]

theorem sylow_inf_centralizer_eq_plane (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    {x z : G} {T : Subgroup G}
    (hf : Prop627Failure G 3 P M x z T)
    (hR : Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2)) :
    (P : Subgroup G) ⊓ centralizer ({x} : Set G) = zpowers x ⊔ zpowers z := by
  have hx1 : x ≠ 1 := hf.point.ne_one
  have hx3 : x ^ 3 = 1 := hf.point.pow_eq_one
  have hz3 : z ^ 3 = 1 := hf.central.pow_eq_one
  have hxz : x * z = z * x := mem_centralizer_iff.mp hf.central.centralizes x hf.point.mem
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hzC : z ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr hxz.symm
  have hzN : zpowers z ≤ normalizer (smallRankS x T : Set G) := hf.z_le_normalizer_S
  have hzS : z ∈ normalizer (smallRankS x T : Set G) := hzN (mem_zpowers z)
  have hS2 : IsPGroup 2 (smallRankS x T) := hf.S_isPGroup
  have hR1 : ⁅zpowers z, smallRankS x T⁆ ≠ ⊥ := hf.R_ne_bot hS
  have hSC : smallRankS x T ≤ centralizer ({x} : Set G) := inf_le_right
  have hRS : smallRankR x z T ≤ smallRankS x T := r10a24_commutator_le_of_normalizes hzN
  have hRC : smallRankR x z T ≤ centralizer ({x} : Set G) := hRS.trans hSC
  have hxR : x ∈ centralizer (smallRankR x z T : Set G) :=
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hRC hh)
  have hzR : z ∉ centralizer (smallRankR x z T : Set G) :=
    not_mem_centralizer_commutator hS2 hz3 hzS hR1
  have hPG : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
  have hA3 : ∃ A : Subgroup G, A ≤ (P : Subgroup G) ∧ IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 3 := by
    obtain ⟨-, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hf.situation.mem_sigmaA
      hf.situation.isCoreMaxLocal
    obtain ⟨A, hAP, hAe, hAc⟩ :=
      CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt (P : Subgroup G)
    rw [hP3] at hAc
    exact ⟨A, hAP, hAe, hAc⟩
  have hrank : CFSG.Open.pRank 3 (centralizer ({x} : Set G)) ≤ 2 := by
    by_contra h
    push Not at h
    exact hf.situation.largeObstruction_empty x
      ⟨hf.sylow_le hS hf.point.mem, hx1, hx3, by omega, hf.point.not_centralizer_le⟩
  have hCx : ∀ E : Subgroup G, E ≤ centralizer ({x} : Set G) → IsElemAbelian 3 E →
      Nat.card E ≤ 3 ^ 2 := by
    intro E hE hEe
    have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk2 := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt hE hEe hk
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hBQ : zpowers x ⊔ zpowers z ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    le_inf hf.B_le_P (sup_le (zpowers_le.mpr hxC) (zpowers_le.mpr hzC))
  refine le_antisymm ?_ hBQ
  by_contra hlt
  have hlt' : zpowers x ⊔ zpowers z < (P : Subgroup G) ⊓ centralizer ({x} : Set G) :=
    lt_of_le_of_ne hBQ (fun h => hlt (le_of_eq h.symm))
  have hQ3 : IsPGroup 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    hPG.to_le inf_le_left
  obtain ⟨g, hgQ, hgB, hg3B⟩ := exists_mem_not_mem_pow_three_mem hQ3 hlt'
  obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.mp hgQ
  have hgx : g * x = x * g := mem_centralizer_singleton_iff.mp hgC
  have hgz : g * z = z * g := mem_centralizer_iff.mp hf.central.centralizes g hgP
  have hgN : g ∈ normalizer (smallRankS x T : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hf.sylowTwo.normalized hgP, le_normalizer hgC⟩
  have hgR : g ∈ normalizer (smallRankR x z T : Set G) :=
    mem_normalizer_commutator_of_commute hgN hgz
  obtain ⟨k, hk⟩ := hPG ⟨g, hgP⟩
  have hgk : g ^ (3 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hg3C : g ^ 3 ∈ centralizer (smallRankR x z T : Set G) :=
    pow_three_mem_centralizer_of_q8 hR hgR (k := k) (by rw [hgk]; exact one_mem _)
  have hg3x : g ^ 3 ∈ zpowers x :=
    mem_zpowers_of_mem_plane_of_mem_centralizer hxz hxR hz3 hzR hg3B hg3C
  have hpl : SmallRankPlane 3 (P : Subgroup G) x z :=
    SmallRankPlane.of_situation hS hf.situation hf.point hf.central
  have hgCB : g ∈ centralizer ((zpowers x ⊔ zpowers z : Subgroup G) : Set G) := by
    refine mem_centralizer_iff.mpr fun h hh => ?_
    have hBc : zpowers x ⊔ zpowers z ≤ centralizer ({g} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hgx.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hgz.symm))
    exact mem_centralizer_singleton_iff.mp (hBc hh)
  have hg3ne : g ^ 3 ≠ 1 := fun h1 => hgB (hpl.mem_of_mem_centralizer g hgCB h1)
  obtain ⟨n, hxn⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hg3x)
  have hred : ∀ m : ℕ, x ^ m = x ^ (m % 3) := fun m => r10a24_pow_eq_pow_mod hx3 m
  have hn3 : n % 3 ≠ 0 := by
    intro h0
    apply hg3ne
    rw [← hxn, hred n, h0, pow_zero]
  have hsq : n * n % 3 = 1 := by
    rcases (by omega : n % 3 = 1 ∨ n % 3 = 2) with h | h <;> rw [Nat.mul_mod, h] <;> norm_num
  have hqcube : (g ^ n) ^ 3 = x := by
    rw [← pow_mul, mul_comm, pow_mul, ← hxn, ← pow_mul, hred (n * n), hsq, pow_one]
  have hqP : g ^ n ∈ (P : Subgroup G) := pow_mem hgP n
  exact sr630b_not_pow_of_rank Nat.prime_three (by norm_num) hPG hx3 hqP hqcube hA3 hCx

end R10C4

section R10C5

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem r10a25_mem_normalizer_centralizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (centralizer (H : Set G) : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ c ∈ centralizer (H : Set G),
      g * c * g⁻¹ ∈ centralizer (H : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro h hh
    have hh' : g⁻¹ * h * g ∈ H := by
      have := (mem_set_normalizer_iff.mp (inv_mem hg) h).mp hh
      simpa using this
    have hc' : g⁻¹ * h * g * c = c * (g⁻¹ * h * g) := mem_centralizer_iff.mp hc _ hh'
    calc h * (g * c * g⁻¹) = g * (g⁻¹ * h * g * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc']
      _ = g * c * g⁻¹ * h := by group
  rw [mem_set_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using this

private theorem r10a25_exists_sylow_le [Finite G] {p : ℕ} [Fact p.Prime] {B H : Subgroup G}
    (hBH : B ≤ H) (hB : IsPGroup p B) : ∃ W : Subgroup G, IsSylowOf p W H ∧ B ≤ W := by
  have hB' : IsPGroup p (B.subgroupOf H) := hB.comap_subtype
  obtain ⟨S, hS⟩ := hB'.exists_le_sylow
  refine ⟨(S : Subgroup H).map H.subtype, ⟨S, rfl⟩, fun b hb => ?_⟩
  exact ⟨⟨b, hBH hb⟩, hS (show (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H from hb), rfl⟩

private theorem r10a25_core {F : Subgroup G} {x z : G} (hxC : x ∈ centralizer (F : Set G))
    (hzN : z ∈ normalizer (F : Set G)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxsyl : IsSylowOf 3 (zpowers x) (centralizer (F : Set G)))
    (hBC : IsSylowOf 3 (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G))) :
    IsSylowOf 3 (zpowers x ⊔ zpowers z) (normalizer (F : Set G)) := by
  have hCN : centralizer (F : Set G) ≤ normalizer (F : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hBN : zpowers x ⊔ zpowers z ≤ normalizer (F : Set G) :=
    sup_le (zpowers_le.mpr (hCN hxC)) (zpowers_le.mpr hzN)
  obtain ⟨W, hW, hBW⟩ := r10a25_exists_sylow_le hBN hBC.isPGroup
  have hNC : normalizer (F : Set G) ≤ normalizer (centralizer (F : Set G) : Set G) :=
    fun g hg => r10a25_mem_normalizer_centralizer hg
  have hWC : IsSylowOf 3 (W ⊓ centralizer (F : Set G)) (centralizer (F : Set G)) :=
    hW.inf_of_le_normalizer hCN hNC
  have hcardX : Nat.card (zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hxW : zpowers x ≤ W ⊓ centralizer (F : Set G) :=
    le_inf ((le_sup_left : zpowers x ≤ zpowers x ⊔ zpowers z).trans hBW)
      (zpowers_le.mpr hxC)
  have hWXeq : W ⊓ centralizer (F : Set G) = zpowers x :=
    (Subgroup.eq_of_le_of_card_ge hxW (hWC.card_eq.trans hxsyl.card_eq.symm).le).symm
  have hWnorm : W ≤ normalizer (zpowers x : Set G) := by
    intro w hw
    have hwC : w ∈ normalizer (centralizer (F : Set G) : Set G) := hNC (hW.le hw)
    have hcong : ∀ h : G, h ∈ W ↔ w * h * w⁻¹ ∈ W := fun h =>
      ⟨fun hh => mul_mem (mul_mem hw hh) (inv_mem hw), fun hh => by
        have := mul_mem (mul_mem (inv_mem hw) hh) hw
        rwa [show w⁻¹ * (w * h * w⁻¹) * w = h by group] at this⟩
    rw [← hWXeq, mem_set_normalizer_iff]
    intro h
    simp only [SetLike.mem_coe, Subgroup.mem_inf]
    exact and_congr (hcong h) (mem_set_normalizer_iff.mp hwC h)
  have hWcent : W ≤ centralizer (zpowers x : Set G) :=
    le_centralizer_of_isPGroup_of_normalizes hW.isPGroup hcardX hWnorm
  have hWCx : W ≤ centralizer ({x} : Set G) := by
    intro w hw
    have h1 : x * w = w * x := mem_centralizer_iff.mp (hWcent hw) x (mem_zpowers x)
    exact mem_centralizer_singleton_iff.mpr h1.symm
  have hWB : W = zpowers x ⊔ zpowers z := hBC.eq_of_le hBW hWCx hW.isPGroup
  rw [← hWB]
  exact hW

theorem isSylowOf_plane_normalizer (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    {T : Subgroup G} {f : ℕ} (hyp : Lemma630Hyp G 3 P M x z T f) :
    IsSylowOf 3 (zpowers x ⊔ zpowers z) (normalizer (smallRankF 3 f x : Set G)) := by
  have hF := facts630 hS hyp
  have hPlane : (P : Subgroup G) ⊓ centralizer ({x} : Set G) = zpowers x ⊔ zpowers z :=
    sylow_inf_centralizer_eq_plane hS hyp.failure (hyp.lemma628.2.1 rfl)
  have hPx : IsSylowOf 3 ((P : Subgroup G) ⊓ centralizer ({x} : Set G))
      (centralizer ({x} : Set G)) :=
    isSylowOf_iff.mpr
      ⟨inf_le_right, P.isPGroup'.to_inf_left, hyp.failure.point.sylow_centralizer⟩
  have hBC : IsSylowOf 3 (zpowers x ⊔ zpowers z) (centralizer ({x} : Set G)) := by
    rw [← hPlane]
    exact hPx
  exact r10a25_core hF.x_C hF.z_N hF.x_three hF.x_ne hF.x_sylow hBC

end R10C5

section R10C7

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a27_commutator_le (S : Subgroup G) {z : G}
    (hz : zpowers z ≤ normalizer (S : Set G)) : ⁅zpowers z, S⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hab : a * b * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hz ha) b).mp hb
  rw [commutatorElement_def]
  exact S.mul_mem hab (S.inv_mem hb)

theorem mem_normalizer_S0 {P : Sylow 3 G} {M : Subgroup G} {x z : G} {T : Subgroup G}
    (hf : Prop627Failure G 3 P M x z T) :
    ∀ g ∈ M ⊓ centralizer ({x} : Set G),
      g ∈ normalizer ((smallRankS x T ⊓ pCoreOf 2 M : Subgroup G) : Set G) := by
  intro g hg
  have hnorm : ((pCoreOf 2 M).subgroupOf M).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 M M le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hMN : M ≤ normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    le_normalizer_of_normal_subgroupOf (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 M)
  have hEq : (smallRankS x T ⊓ pCoreOf 2 M : Subgroup G) =
      centralizer ({x} : Set G) ⊓ pCoreOf 2 M := by
    unfold smallRankS
    rw [inf_right_comm, inf_eq_right.mpr hf.pCoreOf_two_le_T, inf_comm]
  rw [hEq]
  exact inf_normalizer_le_normalizer_inf
    ⟨le_normalizer (Subgroup.mem_inf.mp hg).2, hMN (Subgroup.mem_inf.mp hg).1⟩

theorem x_mem_centralizer_S0 {x : G} {T M : Subgroup G} :
    x ∈ centralizer ((smallRankS x T ⊓ pCoreOf 2 M : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ smallRankS x T ⊓ pCoreOf 2 M := hh
  have hS : h ∈ T ⊓ centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hh').1
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hS).2

theorem z_not_mem_centralizer_S0 (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G} {x z : G}
    {T : Subgroup G} {f : ℕ} (hyp : Lemma630Hyp G 3 P M x z T f) :
    z ∉ centralizer ((smallRankS x T ⊓ pCoreOf 2 M : Subgroup G) : Set G) := by
  obtain ⟨hf, -, -, -, -, -, h29⟩ := hyp
  intro hz
  have hRN : smallRankR x z T ≤ pCoreOf 2 M := h29.2.1
  have hRS : smallRankR x z T ≤ smallRankS x T :=
    r10a27_commutator_le (smallRankS x T) hf.z_le_normalizer_S
  have hRS0 : smallRankR x z T ≤ smallRankS x T ⊓ pCoreOf 2 M := le_inf hRS hRN
  have hzR : z ∈ centralizer ((smallRankR x z T : Subgroup G) : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRS0) hz
  exact not_mem_centralizer_commutator hf.S_isPGroup hf.central.pow_eq_one
    (hf.z_le_normalizer_S (mem_zpowers z)) (hf.R_ne_bot hS) hzR

end R10C7

section R10C6

open CFSG.Open CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem r10a26_le_normalizer_pCoreOf (M : Subgroup G) :
    M ≤ normalizer (pCoreOf 2 M : Set G) := by
  have hnorm : ((pCoreOf 2 M).subgroupOf M).Normal :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf 2 M M le_rfl
      (by rw [Subgroup.subgroupOf_self]; infer_instance)
  exact le_normalizer_of_normal_subgroupOf
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le 2 M)

private theorem r10a26_S0_eq (x : G) (T M : Subgroup G) (hQT : pCoreOf 2 M ≤ T) :
    smallRankS x T ⊓ pCoreOf 2 M = pCoreOf 2 M ⊓ centralizer ({x} : Set G) := by
  unfold smallRankS
  ext y
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨⟨_, hC⟩, hQ⟩
    exact ⟨hQ, hC⟩
  · rintro ⟨hQ, hC⟩
    exact ⟨⟨hQT hQ, hC⟩, hQ⟩

private theorem r10a26_normal_S0 (x : G) (T M : Subgroup G) (hSM : smallRankS x T ≤ M) :
    ((smallRankS x T ⊓ pCoreOf 2 M).subgroupOf (smallRankS x T)).Normal := by
  have hSN : smallRankS x T ≤ normalizer ((smallRankS x T ⊓ pCoreOf 2 M : Subgroup G) : Set G) :=
    fun s hs => inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨le_normalizer hs, r10a26_le_normalizer_pCoreOf M (hSM hs)⟩)
  exact (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hSN

private theorem r10a26_commutator_le_S (x z : G) (T : Subgroup G)
    (hz : zpowers z ≤ normalizer (smallRankS x T : Set G)) :
    smallRankR x z T ≤ smallRankS x T := by
  unfold smallRankR
  refine Subgroup.commutator_le.mpr ?_
  intro g₁ hg₁ g₂ hg₂
  rw [commutatorElement_def]
  have h1 : g₁ * g₂ * g₁⁻¹ ∈ smallRankS x T :=
    (mem_normalizer_iff.mp (hz hg₁) g₂).mp hg₂
  exact (smallRankS x T).mul_mem h1 ((smallRankS x T).inv_mem hg₂)

theorem mem_centralizer_S0_of_coprime (hS : Setting G) (hOut : KFactOutQ8Quaternion)
    {P : Sylow 3 G} {M : Subgroup G} {x z : G} {T : Subgroup G} {f : ℕ}
    (hyp : Lemma630Hyp G 3 P M x z T f) :
    ∀ g ∈ M ⊓ centralizer ({x} : Set G), Nat.Coprime (orderOf g) 6 →
      g ∈ centralizer ((smallRankS x T ⊓ pCoreOf 2 M : Subgroup G) : Set G) := by
  obtain ⟨hf, -, h28, -, -, -, h29⟩ := hyp
  obtain ⟨n, hQ⟩ := h29.1.2.1 rfl
  have hR : Nonempty (↥(smallRankR x z T) ≃* QuaternionGroup 2) := h28.2.1 rfl
  have hRQ : smallRankR x z T ≤ pCoreOf 2 M := h29.2.1
  have hQT : pCoreOf 2 M ≤ T := hf.pCoreOf_two_le_T
  have hSM : smallRankS x T ≤ M := hf.S_le_M
  have hRS : smallRankR x z T ≤ smallRankS x T :=
    r10a26_commutator_le_S x z T hf.z_le_normalizer_S
  have hRS₀ : smallRankR x z T ≤ smallRankS x T ⊓ pCoreOf 2 M := le_inf hRS hRQ
  intro g hg hcop
  obtain ⟨hgM, hgC⟩ := Subgroup.mem_inf.mp hg
  have hgnorm : g ∈ normalizer ((smallRankS x T ⊓ pCoreOf 2 M : Subgroup G) : Set G) := by
    rw [r10a26_S0_eq x T M hQT]
    exact inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨r10a26_le_normalizer_pCoreOf M hgM, le_normalizer hgC⟩)
  exact hOut G (smallRankS x T) (smallRankS x T ⊓ pCoreOf 2 M) (smallRankR x z T) n hQ
    inf_le_left (r10a26_normal_S0 x T M hSM) hRS₀ hR g hgnorm hcop

end R10C6

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
