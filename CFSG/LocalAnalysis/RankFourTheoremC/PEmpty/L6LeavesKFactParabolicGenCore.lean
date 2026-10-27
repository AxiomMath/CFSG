module

public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.LieType.BorelTits Subgroup

variable {G : Type*} [Group G]

@[expose] def parabGen (W : Subgroup G) : Subgroup G :=
  ⨆ (P : Subgroup G) (_ : normalizer (W : Set G) ≤ P ∧ pCoreOf 2 P ≠ ⊥), P

theorem le_parabGen {W P : Subgroup G} (hN : normalizer (W : Set G) ≤ P)
    (hP : pCoreOf 2 P ≠ ⊥) : P ≤ parabGen W :=
  le_iSup₂_of_le (f := fun (P : Subgroup G)
    (_ : normalizer (W : Set G) ≤ P ∧ pCoreOf 2 P ≠ ⊥) => P) P ⟨hN, hP⟩ le_rfl

theorem pCoreOf_le_sylow [Finite G] (W : Sylow 2 G) {P : Subgroup G} (hWP : (W : Subgroup G) ≤ P) :
    pCoreOf 2 P ≤ (W : Subgroup G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 P) := pCoreOf_isPGroup 2 P
  have hWN : (W : Subgroup G) ≤ normalizer (pCoreOf 2 P : Set G) :=
    hWP.trans (le_normalizer_pCoreOf 2 P)
  have hsup : IsPGroup 2 ((W : Subgroup G) ⊔ pCoreOf 2 P : Subgroup G) :=
    W.isPGroup'.to_sup_of_normal_right' hQ2 hWN
  have := W.is_maximal' hsup le_sup_left
  exact le_sup_right.trans this.le

theorem parabGen_le_of_hyp [Finite G] (W : Sylow 2 G) {J : Subgroup G}
    (hJ : ∀ Q : Subgroup G, Q ≤ (W : Subgroup G) → Q ≠ ⊥ →
      normalizer ((W : Subgroup G) : Set G) ≤ normalizer (Q : Set G) →
        normalizer (Q : Set G) ≤ J) :
    parabGen (W : Subgroup G) ≤ J := by
  refine iSup₂_le fun P hP => ?_
  obtain ⟨hNP, hcore⟩ := hP
  have hWP : (W : Subgroup G) ≤ P := le_normalizer.trans hNP
  have hPQ : P ≤ normalizer (pCoreOf 2 P : Set G) := le_normalizer_pCoreOf 2 P
  exact hPQ.trans (hJ _ (pCoreOf_le_sylow W hWP) hcore (hNP.trans hPQ))

@[expose] def HasParGen (G : Type*) [Group G] : Prop :=
  ∃ W : Sylow 2 G, parabGen (W : Subgroup G) = ⊤

theorem mem_of_sup_central {W Z : Subgroup G} [Z.Normal] (hZ : Z ≤ center G)
    (hodd : ∀ x ∈ Z, Odd (orderOf x)) {y : G} (hy : y ∈ W ⊔ Z) (m : ℕ) (hym : y ^ 2 ^ m = 1) :
    y ∈ W := by
  obtain ⟨w, hw, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hcomm : Commute w k := (Subgroup.mem_center_iff.mp (hZ hk) w)
  rw [hcomm.mul_pow] at hym
  have hkW : k ^ 2 ^ m ∈ W := by
    have : k ^ 2 ^ m = (w ^ 2 ^ m)⁻¹ := eq_inv_of_mul_eq_one_right hym
    rw [this]
    exact W.inv_mem (W.pow_mem hw _)
  have hcop : Nat.Coprime (2 ^ m) (orderOf k) :=
    (Nat.coprime_two_left.2 (hodd k hk)).pow_left m
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hcop
  have hkW' : k ∈ W := by
    rw [← ha]
    exact W.pow_mem hkW a
  exact W.mul_mem hw hkW'

theorem normalizer_map_le [Finite G] {G' : Type*} [Group G'] (ψ : G →* G')
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center G)
    (hodd : ∀ x ∈ ψ.ker, Odd (orderOf x)) (W : Sylow 2 G) :
    normalizer (((W : Subgroup G).map ψ : Subgroup G') : Set G') ≤
      (normalizer ((W : Subgroup G) : Set G)).map ψ := by
  have hone : ∀ g : G, ψ g ∈ normalizer (((W : Subgroup G).map ψ : Subgroup G') : Set G') →
      ∀ w ∈ (W : Subgroup G), g * w * g⁻¹ ∈ (W : Subgroup G) := by
    intro g hg w hw
    have h1 : ψ (g * w * g⁻¹) ∈ (W : Subgroup G).map ψ := by
      have := (mem_normalizer_iff.mp hg (ψ w)).mp (Subgroup.mem_map_of_mem ψ hw)
      simpa using this
    have h2 : g * w * g⁻¹ ∈ (W : Subgroup G) ⊔ ψ.ker := by
      rw [← Subgroup.comap_map_eq]
      exact h1
    obtain ⟨m, hm⟩ := W.isPGroup' ⟨w, hw⟩
    have hm' : w ^ 2 ^ m = 1 := congrArg Subtype.val hm
    refine mem_of_sup_central hker hodd h2 m ?_
    rw [conj_pow, hm']
    simp
  rintro g' hg'
  obtain ⟨g, rfl⟩ := hψ g'
  refine ⟨g, ?_, rfl⟩
  show g ∈ normalizer ((W : Subgroup G) : Set G)
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hone g hg' h hh
  · intro hh
    have hg'' : ψ g⁻¹ ∈ normalizer (((W : Subgroup G).map ψ : Subgroup G') : Set G') := by
      rw [map_inv]
      exact (normalizer _).inv_mem hg'
    have := hone g⁻¹ hg'' _ hh
    simpa [mul_assoc] using this

theorem map_parabGen_le [Finite G] {G' : Type*} [Group G'] (ψ : G →* G')
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center G)
    (hodd : ∀ x ∈ ψ.ker, Odd (orderOf x)) (W : Sylow 2 G) :
    (parabGen (W : Subgroup G)).map ψ ≤ parabGen ((W : Subgroup G).map ψ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun P hP => ?_
  obtain ⟨hNP, hcore⟩ := hP
  rw [← Subgroup.map_le_iff_le_comap]
  set Q := pCoreOf 2 P with hQ
  have hQ2 : IsPGroup 2 Q := pCoreOf_isPGroup 2 P
  have hQP : P ≤ normalizer (Q : Set G) := le_normalizer_pCoreOf 2 P
  have hQ' : Q ≤ P := pCoreOf_le 2 P
  have hker_trivial : Q ⊓ ψ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hx.1⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hodd' := hodd x hx.2
    have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
      (Nat.coprime_two_right.2 hodd').pow_right k
    have h1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h1)
  have hmapQ : Q.map ψ ≠ ⊥ := by
    intro hbot
    apply hcore
    rw [Subgroup.map_eq_bot_iff] at hbot
    exact eq_bot_iff.mpr (hker_trivial ▸ le_inf le_rfl hbot)
  have hQmap2 : IsPGroup 2 (Q.map ψ) := hQ2.map ψ
  have hQcore : Q.map ψ ≤ pCoreOf 2 (P.map ψ) := by
    refine le_pCoreOf_of_le_normalizer 2 (Subgroup.map_mono hQ') ?_ hQmap2
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨p * q * p⁻¹, (mem_normalizer_iff.mp (hQP hp) q).mp hq, by simp⟩
    · rintro ⟨q, hq, hqy⟩
      refine ⟨p⁻¹ * q * p, ?_, ?_⟩
      · have := (mem_normalizer_iff.mp (hQP (P.inv_mem hp)) q).mp hq
        simpa using this
      · simp only [map_mul, map_inv] at hqy ⊢
        rw [hqy]
        group
  refine le_parabGen ?_ ?_
  · exact (normalizer_map_le ψ hψ hker hodd W).trans (Subgroup.map_mono hNP)
  · intro hbot
    exact hmapQ (eq_bot_iff.mpr (hQcore.trans hbot.le))

theorem hasParGen_of_surjective [Finite G] {G' : Type*} [Group G'] (ψ : G →* G')
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center G)
    (hodd : ∀ x ∈ ψ.ker, Odd (orderOf x)) (h : HasParGen G) : HasParGen G' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W, hW⟩ := h
  refine ⟨W.mapSurjective hψ, ?_⟩
  rw [Sylow.coe_mapSurjective]
  have := map_parabGen_le ψ hψ hker hodd W
  rw [hW, Subgroup.map_top_of_surjective ψ hψ] at this
  exact top_le_iff.mp this

theorem mulEquiv_ker_le_center {G' : Type*} [Group G'] (e : G ≃* G') :
    e.toMonoidHom.ker ≤ center G := by
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
  exact bot_le

theorem mulEquiv_ker_odd {G' : Type*} [Group G'] (e : G ≃* G') :
    ∀ x ∈ e.toMonoidHom.ker, Odd (orderOf x) := by
  intro x hx
  rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective, Subgroup.mem_bot] at hx
  rw [hx, orderOf_one]
  exact odd_one

theorem hasParGen_of_mulEquiv [Finite G] {G' : Type*} [Group G'] (e : G ≃* G') (h : HasParGen G) :
    HasParGen G' :=
  hasParGen_of_surjective e.toMonoidHom e.surjective (mulEquiv_ker_le_center e)
    (mulEquiv_ker_odd e) h

theorem hasParGen_iff_forall [Finite G] :
    HasParGen G ↔ ∀ W : Sylow 2 G, parabGen (W : Subgroup G) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun ⟨W, hW⟩ W' => ?_, fun h => ⟨Nonempty.some inferInstance, h _⟩⟩
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G W W'
  have hconj : ((g • W : Sylow 2 G) : Subgroup G) =
      (W : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  rw [hconj]
  have := map_parabGen_le (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective
    (mulEquiv_ker_le_center (MulAut.conj g)) (mulEquiv_ker_odd (MulAut.conj g)) W
  rw [hW, Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at this
  exact top_le_iff.mp this

theorem parabGen_eq_top_of_family {ι : Type*} {W : Subgroup G} (P : ι → Subgroup G)
    (hN : ∀ i, normalizer (W : Set G) ≤ P i) (hcore : ∀ i, pCoreOf 2 (P i) ≠ ⊥)
    (hgen : ⨆ i, P i = ⊤) : parabGen W = ⊤ := by
  rw [eq_top_iff, ← hgen]
  exact iSup_le fun i => le_parabGen (hN i) (hcore i)

structure ParFam (G : Type*) [Group G] (ι : Type) where
  W : Sylow 2 G
  P : ι → Subgroup G
  Q : ι → Subgroup G
  nonempty : Nonempty ι
  normalizer_le : ∀ i, normalizer ((W : Subgroup G) : Set G) ≤ P i
  gen : ⨆ i, P i = ⊤
  isPGroup : ∀ i, IsPGroup 2 (Q i)
  le : ∀ i, Q i ≤ P i
  normalizes : ∀ i, P i ≤ normalizer (Q i : Set G)
  ne_bot : ∀ i, Q i ≠ ⊥

theorem ParFam.hasParGen {ι : Type} (F : ParFam G ι) : HasParGen G := by
  refine ⟨F.W, parabGen_eq_top_of_family F.P F.normalizer_le (fun i hbot => ?_) F.gen⟩
  have hle := le_pCoreOf_of_le_normalizer 2 (F.le i) (F.normalizes i) (F.isPGroup i)
  rw [hbot, le_bot_iff] at hle
  exact F.ne_bot i hle

theorem exists_parFam_of_bn_family [Finite G] {ι : Type} [Nonempty ι] {B : Subgroup G}
    (hW : ∃ W : Sylow 2 G, normalizer ((W : Subgroup G) : Set G) = B) (n : ι → G)
    (Q : ι → Subgroup G) (hgen : B ⊔ ⨆ i, zpowers (n i) = ⊤) (hQ2 : ∀ i, IsPGroup 2 (Q i))
    (hQne : ∀ i, Q i ≠ ⊥) (hQB : ∀ i, Q i ≤ B) (hBQ : ∀ i, B ≤ normalizer (Q i : Set G))
    (hnQ : ∀ i, n i ∈ normalizer (Q i : Set G)) : ∃ F : ParFam G ι, F.Q = Q := by
  obtain ⟨W, hW⟩ := hW
  refine ⟨⟨W, fun i => B ⊔ zpowers (n i), Q, ‹Nonempty ι›, fun i => hW.le.trans le_sup_left, ?_,
    hQ2, fun i => (hQB i).trans le_sup_left, fun i => ?_, hQne⟩, rfl⟩
  · obtain ⟨i0⟩ := ‹Nonempty ι›
    have hBle : B ≤ ⨆ i, B ⊔ zpowers (n i) := le_iSup_of_le i0 le_sup_left
    rw [eq_top_iff, ← hgen]
    refine sup_le hBle (iSup_le fun i => ?_)
    exact (le_sup_right : zpowers (n i) ≤ B ⊔ zpowers (n i)).trans
      (le_iSup (fun i => B ⊔ zpowers (n i)) i)
  · exact sup_le (hBQ i) (zpowers_le.mpr (hnQ i))

theorem mem_normalizer_subgroupOf {M : Type*} [Group M] {A R : Subgroup M} (hRA : R ≤ A) {x : M}
    (hxA : x ∈ A) (hx : x ∈ normalizer (R : Set M)) :
    (⟨x, hxA⟩ : A) ∈ normalizer ((R.subgroupOf A : Subgroup A) : Set A) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hRA]
  exact hx

theorem hasParGen_of_bn_family [Finite G] {ι : Type} [Nonempty ι] {B : Subgroup G}
    (hW : ∃ W : Sylow 2 G, normalizer ((W : Subgroup G) : Set G) = B) (n : ι → G)
    (Q : ι → Subgroup G) (hgen : B ⊔ ⨆ i, zpowers (n i) = ⊤) (hQ2 : ∀ i, IsPGroup 2 (Q i))
    (hQne : ∀ i, Q i ≠ ⊥) (hQB : ∀ i, Q i ≤ B) (hBQ : ∀ i, B ≤ normalizer (Q i : Set G))
    (hnQ : ∀ i, n i ∈ normalizer (Q i : Set G)) : HasParGen G :=
  (exists_parFam_of_bn_family hW n Q hgen hQ2 hQne hQB hBQ hnQ).choose.hasParGen

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
