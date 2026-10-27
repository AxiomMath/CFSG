module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627FourGroup
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627WreathR
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankCase
import CFSG.LocalAnalysis.RankThreeTheoremC.TransitivityReduction
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeRankTwo

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

section Helpers

omit [Finite G]

private theorem exists_planeCoord {x z : G} (hx : x ^ 3 = 1) (hz : z ^ 3 = 1)
    (hxz : Commute x z) : ∃ φ : Multiplicative (ZMod 3 × ZMod 3) →* G,
      ∀ a b : ZMod 3, φ (Multiplicative.ofAdd (a, b)) = x ^ a.val * z ^ b.val := by
  refine ⟨{ toFun := fun v => x ^ (Multiplicative.toAdd v).1.val *
              z ^ (Multiplicative.toAdd v).2.val
            map_one' := by simp
            map_mul' := fun v w => ?_ }, fun a b => rfl⟩
  simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
  rw [← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hz, pow_add, pow_add]
  simp only [mul_assoc]
  rw [(hxz.pow_pow _ _).left_comm]

private theorem lines_of_ne_zero {a b c d : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hd : d ≠ 0) :
    (c, d) = (a, b) ∨ (c, d) = 2 • (a, b) ∨ (c, d) = (a, -b) ∨ (c, d) = 2 • (a, -b) := by
  revert a b c d
  decide

private theorem smul_mk_zero_self {d : ZMod 3} (hd : d ≠ 0) :
    d • ((0 : ZMod 3), d) = (0, 1) := by
  revert d
  decide

private theorem smul_mk_self_zero {c : ZMod 3} (hc : c ≠ 0) :
    c • (c, (0 : ZMod 3)) = (1, 0) := by
  revert c
  decide

private theorem centralizer_singleton_le_pow (y : G) (k : ℕ) :
    centralizer ({y} : Set G) ≤ centralizer ({y ^ k} : Set G) := fun _ hg =>
  mem_centralizer_singleton_iff.mpr (Commute.pow_right (mem_centralizer_singleton_iff.mp hg) k).eq

private theorem mem_normalizer_inf {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) :=
  mem_normalizer_iff.mpr fun h =>
    mem_inf.trans ((and_congr (mem_normalizer_iff.mp hH h) (mem_normalizer_iff.mp hK h)).trans
      mem_inf.symm)

private theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext h
  rw [mem_map_equiv, MulAut.conj_symm_apply]
  have := mem_normalizer_iff.mp (inv_mem hg) h
  rw [inv_inv] at this
  exact this.symm

private theorem le_normalizer_iSup_map_conj (Γ U : Subgroup G) :
    Γ ≤ normalizer ((⨆ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  have key : ∀ r ∈ Γ, (⨆ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj r).toMonoidHom ≤ ⨆ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom := by
    intro r hr
    simp only [Subgroup.map_iSup, map_map]
    refine iSup₂_le fun g hg => le_iSup₂_of_le (r * g) (mul_mem hr hg) ?_
    have : (MulAut.conj r).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (r * g)).toMonoidHom := by
      ext w
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
  intro r hr
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key r hr ⟨h, hh, rfl⟩
  · intro hh
    have := key r⁻¹ (inv_mem hr) ⟨_, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

private structure IsFourGroupAt (M B : Subgroup G) (y : G) (V : Subgroup G) : Prop where
  eq_of_normalized : ∀ S : Subgroup G, S ≤ V → S ≠ ⊥ → B ≤ normalizer (S : Set G) → S = V
  le_or_le : ∀ S : Subgroup G, IsPGroup 2 S → S ≤ centralizer ({y} : Set G) →
    B ≤ normalizer (S : Set G) → S ≤ M ∨ S ≤ V

private theorem IsFourGroupAt.map {M B : Subgroup G} {y : G} {V : Subgroup G}
    (h : IsFourGroupAt M B y V) (φ : G ≃* G) (hM : M.map φ.toMonoidHom = M)
    (hB : B.map φ.toMonoidHom = B) : IsFourGroupAt M B (φ y) (V.map φ.toMonoidHom) := by
  have hback : ∀ S : Subgroup G, (S.map φ.symm.toMonoidHom).map φ.toMonoidHom = S := by
    intro S; ext s; simp
  have hback' : ∀ S : Subgroup G, (S.map φ.toMonoidHom).map φ.symm.toMonoidHom = S := by
    intro S; ext s; simp
  have hB' : B.map φ.symm.toMonoidHom = B := by
    conv_lhs => rw [← hB]
    exact hback' B
  have hBS : ∀ S : Subgroup G, B ≤ normalizer (S : Set G) →
      B ≤ normalizer ((S.map φ.symm.toMonoidHom : Subgroup G) : Set G) := by
    intro S hS
    rw [← map_equiv_normalizer_eq S φ.symm, ← hB']
    exact map_mono hS
  refine ⟨fun S hSV hS1 hSB => ?_, fun S hS2 hSy hSB => ?_⟩
  · have h1 : S.map φ.symm.toMonoidHom ≤ V := by
      have := map_mono (f := φ.symm.toMonoidHom) hSV
      rwa [hback'] at this
    have h2 : S.map φ.symm.toMonoidHom ≠ ⊥ := by
      rwa [Ne, map_eq_bot_iff_of_injective _ φ.symm.injective]
    rw [← h.eq_of_normalized _ h1 h2 (hBS S hSB), hback]
  · have h1 : IsPGroup 2 (S.map φ.symm.toMonoidHom) := hS2.map _
    have h2 : S.map φ.symm.toMonoidHom ≤ centralizer ({y} : Set G) := by
      rintro _ ⟨s, hs, rfl⟩
      rw [mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.mp (hSy hs)
      apply φ.injective
      simpa using this
    rcases h.le_or_le _ h1 h2 (hBS S hSB) with h4 | h4
    · left
      have := map_mono (f := φ.toMonoidHom) h4
      rwa [hback, hM] at this
    · right
      have := map_mono (f := φ.toMonoidHom) h4
      rwa [hback] at this

end Helpers

theorem false_of_smallRankFourGroup (hS : Setting G) (hU0 : FullCoreLocal G)
    (hD2 : TheoremD2 G) (h614 : GL83SmallRankProp614 G) {P : Sylow 3 G} {M : Subgroup G}
    (hsit : SmallRankSituation G 3 P M) (hsolv : Group.IsSolvable M)
    (e : (P : Subgroup G) ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3))) {x z : G}
    (hx : SmallRankPoint P M x) (hz : SmallRankCentral P z) {U : Subgroup G}
    (hU : SmallRankFourGroup M x z U) : False := by
  classical
  have hp : 3 ∈ rankThreeSigmaA G := hsit.mem_sigmaA
  have hM := hsit.isCoreMaxLocal
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hp hM).1
  have hpl := SmallRankPlane.of_situation hS hsit hx hz
  set B : Subgroup G := zpowers x ⊔ zpowers z with hBdef
  set N : Subgroup G := normalizer (U : Set G) with hNdef
  set W : Subgroup G := pCoreOf 2 N with hWdef
  have hxB : x ∈ B := mem_sup_left (mem_zpowers x)
  have hzB : z ∈ B := mem_sup_right (mem_zpowers z)
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hpl.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hxZ : x ∉ zpowers z := by
    intro h
    have hcard := hpl.card_eq
    rw [sup_eq_right.mpr (zpowers_le.mpr h), Nat.card_zpowers,
      orderOf_eq_prime hz.pow_eq_one hz.ne_one] at hcard
    norm_num at hcard
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [hU.card_eq]; norm_num)
  have hUne : U ≠ ⊥ := fun h => by
    have := hU.card_eq
    rw [h, card_bot] at this
    norm_num at this
  have hNloc : IsTwoLocal N := ⟨U, hUne, hU2, rfl⟩
  have hBN : B ≤ N := hU.normalized
  have hUW : U ≤ W := twoLocal_witness_le_pCoreOf U N hU2 rfl
  have hW2 : IsPGroup 2 W := pCoreOf_isPGroup 2 N
  have hWN : W ≤ N := pCoreOf_le 2 N
  have hNW : N ≤ normalizer (W : Set G) := localGroup_le_normalizer_pCoreOf 2 N
  have hNM : ¬ N ≤ M := fun h => hU.not_le (le_normalizer.trans h)
  have hnone : ∀ S : Subgroup G, S ≤ W → S ≤ M → B ≤ normalizer (S : Set G) → S = ⊥ := by
    intro S hSW hSM hBS
    by_contra hS1
    exact hNM (h614 3 P M hsit x z hx hz N hNloc hBN
      ⟨S, le_inf (hSW.trans hWN) hSM, hW2.to_le hSW, hS1, hBS⟩)
  have hBnorm : ∀ y ∈ B,
      B ≤ normalizer ((W ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) :=
    fun y hy b hb => mem_normalizer_inf (hNW (hBN hb))
      (le_normalizer (mem_centralizer_singleton_iff.mpr (hBcomm b hb y hy)))
  have hCz : W ⊓ centralizer ({z} : Set G) = ⊥ :=
    hnone _ inf_le_left (inf_le_right.trans ((centralizer_singleton_le_normalizer_zpowers z).trans
      (normalizer_zpowers_le_of_largeObstruction_empty hS hp hM hsit.largeObstruction_empty
        hz.mem hz.centralizes hz.ne_one hz.pow_eq_one))) (hBnorm z hzB)
  have hA : ∀ y ∈ B, ∀ V : Subgroup G, IsFourGroupAt M B y V →
      W ⊓ centralizer ({y} : Set G) ≠ ⊥ → V ≤ W := by
    intro y hyB V hV hne
    rcases hV.le_or_le _ (hW2.to_le inf_le_left) inf_le_right (hBnorm y hyB) with hle | hle
    · exact absurd (hnone _ inf_le_left hle (hBnorm y hyB)) hne
    · rw [← hV.eq_of_normalized _ hle hne (hBnorm y hyB)]
      exact inf_le_left
  obtain ⟨φ, hφ⟩ := exists_planeCoord hx.pow_eq_one hz.pow_eq_one (hBcomm x hxB z hzB)
  have hφB : ∀ v, φ v ∈ B := fun v => by
    show φ (Multiplicative.ofAdd ((Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2)) ∈ B
    rw [hφ]
    exact mul_mem (mem_sup_left (pow_mem (mem_zpowers x) _))
      (mem_sup_right (pow_mem (mem_zpowers z) _))
  have hval1 : (1 : ZMod 3).val = 1 := rfl
  have hφx : φ (Multiplicative.ofAdd (1, 0)) = x := by rw [hφ, hval1]; simp
  have hφz : φ (Multiplicative.ofAdd (0, 1)) = z := by rw [hφ, hval1]; simp
  have hBφ : ∀ w ∈ B, ∃ c d : ZMod 3, φ (Multiplicative.ofAdd (c, d)) = w := by
    intro w hw
    have hle : B ≤ φ.range := sup_le (zpowers_le.mpr ⟨_, hφx⟩) (zpowers_le.mpr ⟨_, hφz⟩)
    obtain ⟨v, rfl⟩ := hle hw
    exact ⟨(Multiplicative.toAdd v).1, (Multiplicative.toAdd v).2, rfl⟩
  have hpowC : ∀ (k : ℕ) (v : ZMod 3 × ZMod 3),
      W ⊓ centralizer ({φ (Multiplicative.ofAdd v)} : Set G) ≠ ⊥ →
      W ⊓ centralizer ({φ (Multiplicative.ofAdd (k • v))} : Set G) ≠ ⊥ := fun k v h => by
    rw [ofAdd_nsmul, map_pow]
    exact ne_bot_of_le_ne_bot h (inf_le_inf_left _ (centralizer_singleton_le_pow _ k))
  have hC : ∃ a b : ZMod 3, a ≠ 0 ∧ b ≠ 0 ∧
      W ⊓ centralizer ({φ (Multiplicative.ofAdd (a, b))} : Set G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hWx : W ≤ centralizer ({x} : Set G) := by
      refine embedded_rank_two_signalizer_le_of_line_centralizers 3 Nat.prime_three φ W _ ?_ ?_ ?_
      · rintro _ ⟨v, rfl⟩
        exact hNW (hBN (hφB v))
      · obtain ⟨n, hn⟩ := hW2.exists_card_eq
        rw [hn]
        exact Nat.Coprime.pow_right n (by norm_num)
      · rintro ⟨c, d⟩ hv
        have hsub : ∀ k : ZMod 3, W ⊓ centralizer
            ((φ.comp (coordinatePairLineHom (c, d))).range : Set G) ≤
            W ⊓ centralizer ({φ (Multiplicative.ofAdd (k • (c, d)))} : Set G) := fun k =>
          inf_le_inf_left _ (centralizer_le
            (Set.singleton_subset_iff.mpr ⟨Multiplicative.ofAdd k, rfl⟩))
        by_cases hc : c = 0
        · subst hc
          have hd : d ≠ 0 := fun hd => hv (by rw [hd]; rfl)
          refine (hsub d).trans ?_
          rw [smul_mk_zero_self hd, hφz, hCz]
          exact bot_le
        by_cases hd : d = 0
        · subst hd
          refine (hsub c).trans ?_
          rw [smul_mk_self_zero hc, hφx]
          exact inf_le_right
        · refine (hsub 1).trans ?_
          rw [one_smul, hcon c d hc hd]
          exact bot_le
    have hxW : x ∈ W := hS.charTwo N hNloc ⟨hBN hxB, mem_centralizer_iff.mpr fun w hw =>
      mem_centralizer_singleton_iff.mp (hWx hw)⟩
    obtain ⟨k, hk⟩ := hW2 ⟨x, hxW⟩
    have hxk : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h3 : 3 ∣ 2 ^ k := by
      rw [← orderOf_eq_prime hx.pow_eq_one hx.ne_one]
      exact orderOf_dvd_of_pow_eq_one hxk
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at this
  obtain ⟨a, b, ha, hb, hy⟩ := hC
  obtain ⟨t, ⟨htx, htU⟩, htz⟩ := hU.exists_inverting
  have htW : t ∈ normalizer (W : Set G) := hNW htU
  have htx' : t * x * t⁻¹ = x := by
    rw [mem_centralizer_singleton_iff.mp htx, mul_inv_cancel_right]
  have hconj : t * φ (Multiplicative.ofAdd (a, b)) * t⁻¹ = φ (Multiplicative.ofAdd (a, -b)) := by
    have hsplit : φ (Multiplicative.ofAdd (a, -b)) * φ (Multiplicative.ofAdd ((0 : ZMod 3), b)) =
        φ (Multiplicative.ofAdd (a, 0)) := by
      rw [← map_mul]
      congr 1
      exact congrArg Multiplicative.ofAdd (Prod.ext (add_zero a) (neg_add_cancel b))
    rw [eq_mul_inv_of_mul_eq hsplit, hφ, hφ, hφ]
    simp only [ZMod.val_zero, pow_zero, mul_one, one_mul]
    rw [← MulAut.conj_apply, map_mul, map_pow, map_pow, MulAut.conj_apply, MulAut.conj_apply,
      htx', htz, inv_pow]
  have hy' : W ⊓ centralizer ({φ (Multiplicative.ofAdd (a, -b))} : Set G) ≠ ⊥ := by
    obtain ⟨⟨s, hsW, hsy⟩, hs1⟩ := ne_bot_iff_exists_ne_one.mp hy
    have hmem : t * s * t⁻¹ ∈ centralizer ({φ (Multiplicative.ofAdd (a, -b))} : Set G) := by
      rw [← hconj, mem_centralizer_singleton_iff]
      have := mem_centralizer_singleton_iff.mp hsy
      calc t * s * t⁻¹ * (t * φ (Multiplicative.ofAdd (a, b)) * t⁻¹)
          = t * (s * φ (Multiplicative.ofAdd (a, b))) * t⁻¹ := by group
        _ = t * (φ (Multiplicative.ofAdd (a, b)) * s) * t⁻¹ := by rw [this]
        _ = t * φ (Multiplicative.ofAdd (a, b)) * t⁻¹ * (t * s * t⁻¹) := by group
    refine ne_bot_iff_exists_ne_one.mpr
      ⟨⟨t * s * t⁻¹, (mem_normalizer_iff.mp htW s).mp hsW, hmem⟩, fun h => ?_⟩
    exact hs1 (Subtype.ext (conj_eq_one_iff.mp (congrArg Subtype.val h)))
  have hall : ∀ w ∈ B, w ∉ zpowers z → W ⊓ centralizer ({w} : Set G) ≠ ⊥ := by
    intro w hwB hwZ
    obtain ⟨c, d, rfl⟩ := hBφ w hwB
    have hc : c ≠ 0 := by
      rintro rfl
      apply hwZ
      rw [hφ, ZMod.val_zero, pow_zero, one_mul]
      exact pow_mem (mem_zpowers z) _
    by_cases hd : d = 0
    · subst hd
      rw [hφ, ZMod.val_zero, pow_zero, mul_one]
      exact ne_bot_of_le_ne_bot hUne (le_inf hUW (hU.le_centralizer.trans
        (centralizer_singleton_le_pow x _)))
    · rcases lines_of_ne_zero ha hb hc hd with h | h | h | h <;> rw [h]
      · exact hy
      · exact hpowC 2 _ hy
      · exact hy'
      · exact hpowC 2 _ hy'
  have hFour : IsFourGroupAt M B x U := ⟨hU.eq_of_normalized, hU.le_or_le⟩
  set Γ : Subgroup G := (P : Subgroup G) ⊓ normalizer (B : Set G) with hΓdef
  have hUg : ∀ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom ≤ W := by
    intro g hg
    have hgB : g ∈ normalizer (B : Set G) := hg.2
    have hgZ : g ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
      normalizer_plane_le_normalizer_zpowers hS hsit hx hz hgB
    have hgx : MulAut.conj g x ∈ B := (mem_normalizer_iff.mp hgB x).mp hxB
    refine hA _ hgx _ (hFour.map (MulAut.conj g)
      (map_conj_eq_of_mem_normalizer (le_normalizer (hPM hg.1)))
      (map_conj_eq_of_mem_normalizer hgB)) (hall _ hgx fun h => hxZ ?_)
    exact (mem_normalizer_iff.mp hgZ x).mpr h
  set W₀ : Subgroup G := ⨆ g ∈ Γ, U.map (MulAut.conj g).toMonoidHom with hW₀def
  have hW₀W : W₀ ≤ W := iSup₂_le hUg
  have hUW₀ : U ≤ W₀ := le_iSup₂_of_le (1 : G) (one_mem Γ) fun u hu => ⟨u, hu, by simp⟩
  have hΓW₀ : Γ ≤ normalizer (W₀ : Set G) := le_normalizer_iSup_map_conj Γ U
  have hW₀loc : IsTwoLocal (normalizer (W₀ : Set G)) :=
    ⟨W₀, ne_bot_of_le_ne_bot hUne hUW₀, hW2.to_le hW₀W, rfl⟩
  obtain ⟨R, hRP, hRB, hR3, hRnc, hΓR⟩ :=
    exists_noncyclic_le_normalizer_gamma_one_le hS hU0 hsit e hx hz
  have hle : normalizer (W₀ : Set G) ≤ M :=
    hD2 M hM.1 (fun p' hp' P' hM' => hU0 p' hp' P' M hM') (fun h3 P₃ hM₃ =>
      ⟨fun Q hQP hQne hQ3 => normalizer_le_of_three_le_pRank_sup_centralizer hS hU0 h3 hM₃
        hsit.largeObstruction_empty hQP hQne hQ3, fun h => absurd hsolv h⟩) 3 hp P hM _ R hW₀loc
      (fun r hr => hΓW₀ ⟨hRP hr, hRB hr⟩) (hRP.trans hPM) hR3 hRnc hΓR
  exact hU.not_le (hUW₀.trans (le_normalizer.trans hle))

end CFSG.LocalAnalysis.RankThreeTheoremC
