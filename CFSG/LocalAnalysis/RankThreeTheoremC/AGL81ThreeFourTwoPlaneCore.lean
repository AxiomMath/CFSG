module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.A3Structure312Transport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section PlaneCore

theorem exists_ne_one_mem_inf_centralizer_of_inner {Y : Type*} [Group Y] [Finite Y]
    {K : Subgroup Y} [K.Normal] (hZK : center K = ⊥) {p : ℕ}
    (hinn : ∀ φ : MulAut K, φ ^ p = 1 → φ ∈ inner K)
    (hrk : ∀ B : Subgroup K, IsElemAbelian p B → Nat.card B ≤ p ^ 2) {A : Subgroup Y}
    (hA : IsElemAbelian p A) (hcard : p ^ 2 < Nat.card A) :
    ∃ c ∈ A ⊓ centralizer (K : Set Y), c ≠ 1 := by
  haveI : Finite (MulAut K) := Finite.of_injective (fun φ : MulAut K => (φ : K ≃ K))
    (fun φ ψ h => MulEquiv.ext fun x => congrArg (fun f : K ≃ K => f x) h)
  set θ : A →* MulAut K := MulAut.conjNormal.comp A.subtype with hθ
  have hker : ∀ a : A, θ a = 1 → (a : Y) ∈ centralizer (K : Set Y) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro k hk
    have := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) ha
    simp only [hθ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply,
      MulAut.one_apply] at this
    calc k * a = (a * k * (a : Y)⁻¹) * a := by rw [this]
      _ = a * k := by group
  have hinnK : θ.range ≤ inner K := by
    rintro _ ⟨a, rfl⟩
    refine hinn _ ?_
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (hA.2 a a.2)
    rw [this, map_one]
  have hconj : Function.Injective (MulAut.conj : K →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    have : k ∈ center K := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut K => φ g) (MonoidHom.mem_ker.1 hk)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * k = (k * g * k⁻¹) * k := by rw [this]
        _ = k * g := by group
    rw [hZK] at this
    exact this
  set B : Subgroup K := θ.range.comap MulAut.conj with hB
  have hBcard : Nat.card B = Nat.card θ.range := by
    have hmap : B.map MulAut.conj = θ.range := by
      rw [hB, Subgroup.map_comap_eq]
      exact inf_eq_right.2 hinnK
    rw [← hmap, Subgroup.card_map_of_injective hconj]
  have hBel : IsElemAbelian p B := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hconj
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg θ (hA.1.is_comm.comm a b)
    · apply hconj
      obtain ⟨a, ha⟩ := hx
      rw [map_pow, ← ha, ← map_pow, map_one]
      have : a ^ p = 1 := Subtype.ext (hA.2 a a.2)
      rw [this, map_one]
  have hrange : Nat.card θ.range ≤ p ^ 2 := hBcard ▸ hrk B hBel
  have hsplit : Nat.card A = Nat.card θ.range * Nat.card θ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv]
  have hk1 : 1 < Nat.card θ.ker := by
    by_contra h1
    push Not at h1
    have : Nat.card A ≤ p ^ 2 := by
      calc Nat.card A = Nat.card θ.range * Nat.card θ.ker := hsplit
        _ ≤ p ^ 2 * 1 := Nat.mul_le_mul hrange h1
        _ = p ^ 2 := mul_one _
    omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.one_lt_card_iff_ne_bot θ.ker).1 hk1 |>
    (Subgroup.ne_bot_iff_exists_ne_one).1
  refine ⟨a, ⟨a.2, hker a ha⟩, fun h => ha1 ?_⟩
  exact Subtype.ext (Subtype.ext h)

theorem threeFourTwoAt_of_planeCore {p : ℕ} {X : Type*} [Group X] [Finite X]
    (hX : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (hinn : ∀ x : MulAut X, (∃ n : ℕ, x ^ p ^ n = 1) → x ∈ inner X)
    (hrk : ∀ B : Subgroup X, IsElemAbelian p B → Nat.card B ≤ p ^ 2)
    (hrk2 : ∀ S : Sylow p X, ∃ B : Subgroup X, B ≤ S ∧ IsElemAbelian p B ∧ Nat.card B = p ^ 2)
    (hΓ : ∀ S : Sylow p X, GLBCore p 2 (S : Subgroup X) = ⊤)
    (hW : ∀ E W J : Subgroup X, IsElemAbelian p E → Nat.card E = p ^ 2 →
      GLBCore p 1 E ≤ W → W ≠ ⊤ → J ≤ W → J ≠ ⊥ → ⁅J, J⁆ = J → IsSubnormal J W →
      (∃ (Q : Type) (_ : Group Q) (f : J →* Q), Function.Surjective f ∧ IsPGroup 2 f.ker ∧
        CFSG.Open.IsQuasisimple Q) →
      ∃ iK iJ : TauCeti.CFSGIndex, IsThreeFourPair p iK iJ ∧ Nonempty (X ≃* iK.Group) ∧
        ∃ g : J →* iJ.Group, Function.Surjective g) :
    ThreeFourTwoAt p X := by
  haveI := hX
  have hZ : center X = ⊥ := CFSG.ComponentClassification.Helpers.center_eq_bot X hnab
  refine threeFourTwoAt_of_forall_model hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp hp2 hKn e _ _ _ hER hE hEc hcore _ hKY J hJW hJ1 hJp hJs hQ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hKn
  have hp1 : 1 < p := hp.one_lt
  have hes : Function.Surjective e.toMonoidHom := e.surjective
  have hei : Function.Injective e.toMonoidHom := e.injective
  have hZK : center K = ⊥ := by
    have h := Subgroup.map_center_eq e
    rw [hZ] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h
  have hinnK : ∀ φ : MulAut K, φ ^ p = 1 → φ ∈ inner K := by
    intro φ hφ
    have h : MulAut.congr e φ ∈ inner X := hinn _ ⟨1, by rw [pow_one, ← map_pow, hφ, map_one]⟩
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e] at h
    obtain ⟨ψ, hψ, he⟩ := h
    rwa [(MulAut.congr e).injective he] at hψ
  have hrkK : ∀ B : Subgroup K, IsElemAbelian p B → Nat.card B ≤ p ^ 2 := fun B hB => by
    rw [← Subgroup.card_map_of_injective hei]
    exact hrk _ (CFSG.Open.IsElemAbelian.map hB _)
  set W : Subgroup X := (Y₀.subgroupOf K).map e.toMonoidHom with hWdef
  have hWtop : W ≠ ⊤ := by
    intro h
    apply hKY
    have h2 : Y₀.subgroupOf K = ⊤ := by
      apply Subgroup.map_injective hei
      rw [← hWdef, h, Subgroup.map_top_of_surjective _ hes]
    intro k hk
    have : (⟨k, hk⟩ : K) ∈ Y₀.subgroupOf K := h2 ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hnorm : ∀ F : Subgroup K, normalizer ((F.map K.subtype : Subgroup Y) : Set Y) ≤ Y₀ →
      normalizer ((F.map e.toMonoidHom : Subgroup X) : Set X) ≤ W := by
    intro F hF
    rw [← Subgroup.map_equiv_normalizer_eq]
    refine Subgroup.map_mono fun k hk => ?_
    exact Subgroup.mem_subgroupOf.2
      (hF ((CFSG.Quasithin.A312.mem_normalizer_map_subtype_iff K F k).1 hk))
  have hrkY : ∀ F : Subgroup K, CFSG.Open.pRank p (F.map K.subtype) =
      CFSG.Open.pRank p (F.map e.toMonoidHom) := by
    intro F
    rw [← CFSG.SectionRank.pRank_coe_eq_openPRank, ← CFSG.SectionRank.pRank_coe_eq_openPRank,
      CFSG.QuasithinUnique.Setup.Campbell.pRank_map_of_injective p _ K.subtype_injective,
      CFSG.QuasithinUnique.Setup.Campbell.pRank_map_of_injective p _ hei]
  have hKC := CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center hZK
  have hnotK : ∀ c ∈ centralizer (K : Set Y), c ≠ 1 → c ∉ K := fun c hc h1 hcK =>
    h1 (Subgroup.mem_bot.1 (hKC ▸ Subgroup.mem_inf.2 ⟨hcK, hc⟩))
  obtain ⟨SK, hSK⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  set S' : Sylow p X := SK.mapSurjective hes with hS'
  have hS'eq : (S' : Subgroup X) = (SK : Subgroup K).map e.toMonoidHom := rfl
  have hQF : ∀ Q : Subgroup X, (Q.comap e.toMonoidHom).map e.toMonoidHom = Q := fun Q =>
    Subgroup.map_comap_eq_self_of_surjective hes Q
  have hSKR : (SK : Subgroup K).map K.subtype ≤ R := hSK ▸ inf_le_left
  have hbig : ∀ (B : Subgroup Y), B ≤ K → IsElemAbelian p B → ∀ c ∈ centralizer (K : Set Y),
      c ≠ 1 → c ^ p = 1 → IsElemAbelian p (B ⊔ zpowers c) ∧
        Nat.card B < Nat.card ↥(B ⊔ zpowers c) := by
    intro B hBK hB c hc hc1 hcp
    refine ⟨hB.sup_of_commute (CFSG.Open.isElemAbelian_zpowers hcp) fun a ha b hb => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hb
      rw [← hk]
      exact (Commute.zpow_right ((mem_centralizer_iff.1 hc) a (hBK ha)) k).eq
    · refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hnotK c hc hc1 ?_)
      exact hBK (h ▸ (le_sup_right : zpowers c ≤ B ⊔ zpowers c) (mem_zpowers c))
  have hpow : ∀ B : Subgroup Y, IsElemAbelian p B → ∃ m : ℕ, Nat.card B = p ^ m := by
    intro B hB
    exact IsPGroup.iff_card.1 hB.isPGroup
  split_ifs at hcore with h3
  ·
    exfalso
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    obtain ⟨A, hAR, hA, hAc⟩ := CFSG.SectionRank.exists_pRank hp1 (R : Subgroup Y)
    have hA3 : p ^ 2 < Nat.card A := by
      rw [hAc]
      exact Nat.pow_lt_pow_right hp1 (by omega)
    obtain ⟨c, ⟨hcA, hcC⟩, hc1⟩ :=
      exists_ne_one_mem_inf_centralizer_of_inner hZK hinnK hrkK hA hA3
    have hcp : c ^ p = 1 := hA.2 c hcA
    apply hWtop
    rw [eq_top_iff, ← hΓ S']
    refine sSup_le ?_
    rintro _ ⟨Q, hQS, hQ2, rfl⟩
    set F : Subgroup K := Q.comap e.toMonoidHom with hF
    have hFQ : F.map e.toMonoidHom = Q := hQF Q
    rw [← hFQ]
    refine hnorm F (hcore.trans' ?_)
    refine le_sSup ⟨F.map K.subtype, ?_, ?_, ?_, rfl⟩
    · have hFS : F ≤ SK := by
        intro k hk
        have : e k ∈ (S' : Subgroup X) := hQS hk
        rw [hS'eq] at this
        obtain ⟨k', hk', hkk'⟩ := this
        rw [← e.injective hkk']
        exact hk'
      exact (Subgroup.map_mono hFS).trans hSKR
    · rw [hrkY F, hFQ]
      exact hQ2
    · obtain ⟨B, hBF, hB, hBc⟩ := CFSG.SectionRank.exists_pRank hp1 (F.map K.subtype)
      have hBK : B ≤ K := hBF.trans (Subgroup.map_subtype_le F)
      obtain ⟨hBc', hlt⟩ := hbig B hBK hB c hcC hc1 hcp
      obtain ⟨m, hm⟩ := hpow _ hBc'
      have hr2 : 2 ≤ CFSG.Open.pRank p (F.map K.subtype) := by rw [hrkY F, hFQ]; exact hQ2
      have hm3 : 3 ≤ m := by
        have : p ^ CFSG.Open.pRank p (F.map K.subtype) < p ^ m := by rw [← hBc, ← hm]; exact hlt
        have := (Nat.pow_lt_pow_iff_right hp1).1 this
        omega
      refine hm3.trans (CFSG.SectionRank.le_pRank hp1 ?_ hBc' hm)
      refine sup_le (hBF.trans le_sup_left) ((zpowers_le.2 ?_).trans le_sup_right)
      refine Subgroup.mem_inf.2 ⟨hAR hcA, mem_centralizer_iff.2 fun y hy => ?_⟩
      exact (mem_centralizer_iff.1 hcC) y ((Subgroup.map_subtype_le F) hy)
  ·
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    have hCp : ∀ c ∈ centralizer (K : Set Y), c ^ p = 1 → c = 1 := by
      intro c hcC hcp
      by_contra hc1
      obtain ⟨B', hB'S, hB', hB'c⟩ := hrk2 S'
      set B : Subgroup Y := (B'.comap e.toMonoidHom).map K.subtype with hB
      have hBK : B ≤ K := Subgroup.map_subtype_le _
      have hBel : IsElemAbelian p B := CFSG.Open.IsElemAbelian.map (hB'.comap hei) K.subtype
      obtain ⟨hBc', hlt⟩ := hbig B hBK hBel c hcC hc1 hcp
      have hBcard : Nat.card B = p ^ 2 := by
        rw [hB, Subgroup.card_map_of_injective K.subtype_injective, ← hB'c,
          ← Subgroup.card_map_of_injective hei, hQF]
      obtain ⟨m, hm⟩ := hpow _ hBc'
      have hm3 : 3 ≤ m := by
        have : p ^ 2 < p ^ m := by rw [← hBcard, ← hm]; exact hlt
        have := (Nat.pow_lt_pow_iff_right hp1).1 this
        omega
      obtain ⟨R', hR'⟩ := hBc'.isPGroup.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y R' R
      have hle : (B ⊔ zpowers c).map (MulAut.conj g).toMonoidHom ≤ R := by
        rintro _ ⟨x, hx, rfl⟩
        rw [← hg]
        exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) (R' : Subgroup Y) (hR' hx)
      have := CFSG.SectionRank.le_pRank hp1 hle (CFSG.Open.IsElemAbelian.map hBc' _)
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hm])
      omega
    have hEK : E ≤ K := by
      intro r hr
      obtain ⟨t, ht⟩ := hinnK (MulAut.conjNormal r) (by rw [← map_pow, hE.2 r hr, map_one])
      have hkr := CFSG.AGLEmbedding.inv_mul_mem_centralizer_of_conjNormal_eq ht.symm
      set k : Y := (t : Y) with hkdef
      have hk : k ∈ K := t.2
      have hcomm : Commute k (k⁻¹ * r) := (mem_centralizer_iff.1 hkr) k hk
      have hcp : (k⁻¹ * r) ^ p = 1 := by
        have h1 : r ^ p = 1 := hE.2 r hr
        have hrp : r ^ p = k ^ p * (k⁻¹ * r) ^ p := by
          rw [← hcomm.mul_pow, mul_inv_cancel_left]
        have hK1 : (k⁻¹ * r) ^ p ∈ K := by
          have : (k⁻¹ * r) ^ p = (k ^ p)⁻¹ * r ^ p := by rw [hrp, inv_mul_cancel_left]
          rw [this, h1, mul_one]
          exact K.inv_mem (K.pow_mem hk p)
        have hC1 : (k⁻¹ * r) ^ p ∈ centralizer (K : Set Y) := (centralizer _).pow_mem hkr p
        exact Subgroup.mem_bot.1 (hKC ▸ Subgroup.mem_inf.2 ⟨hK1, hC1⟩)
      have := hCp _ hkr hcp
      have hrk' : r = k := by
        have : k * (k⁻¹ * r) = k * 1 := by rw [this]
        simpa using this
      rw [hrk']
      exact hk
    set E' : Subgroup X := (E.subgroupOf K).map e.toMonoidHom with hE'
    have hE'el : IsElemAbelian p E' :=
      CFSG.Open.IsElemAbelian.map (hE.comap K.subtype_injective) _
    have hE'c : Nat.card E' = p ^ 2 := by
      rw [hE', Subgroup.card_map_of_injective hei, ← hEc]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
    have hcoreW : GLBCore p 1 E' ≤ W := by
      refine sSup_le ?_
      rintro _ ⟨Q, hQE, hQ1, rfl⟩
      set F : Subgroup K := Q.comap e.toMonoidHom with hF
      have hFQ : F.map e.toMonoidHom = Q := hQF Q
      rw [← hFQ]
      refine hnorm F (hcore.trans' (le_sSup ⟨F.map K.subtype, ?_, ?_, rfl⟩))
      · rintro _ ⟨k, hk, rfl⟩
        have : e k ∈ E' := hQE hk
        rw [hE'] at this
        obtain ⟨k', hk', hkk'⟩ := this
        rw [← e.injective hkk']
        exact Subgroup.mem_subgroupOf.1 hk'
      · rw [hrkY F, hFQ]
        exact hQ1
    obtain ⟨iK, iJ, hpair, ⟨eK⟩, g, hg⟩ :=
      hW E' W J hE'el hE'c hcoreW hWtop hJW hJ1 hJp hJs hQ
    exact ⟨iK, iJ, hpair, ⟨e.trans eK⟩, g, hg⟩

end PlaneCore

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

end
