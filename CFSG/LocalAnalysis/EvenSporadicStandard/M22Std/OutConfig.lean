module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCAction
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.ThmCOuter

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open CFSG.EvenSporadicStandard.Fin76b
open CFSG.EvenSporadicStandard.Finkelstein77 (innAut)

variable {G : Type} [Group G] {L : Subgroup G}

theorem thetaH_surjective_of_rel [Finite G] (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hMN : centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hout : (innAut (L ⧸ center L)).index ∣ 2)
    (hrel : (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2) :
    Function.Surjective (thetaH hMN) := by
  set R := (thetaH hMN).range with hR
  have hinnR : innAut (L ⧸ center L) ≤ R := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨(l : G), le_centralizer_singleton hz l.2⟩, thetaH_conj hMN hz l⟩
  have hnle : ¬ R ≤ innAut (L ⧸ center L) := by
    intro hle
    have hne : ¬ centralizer ({z} : Set G) ≤ L ⊔ zpowers z := fun h1 =>
      absurd (Subgroup.relIndex_eq_one.2 h1) (by rw [hrel]; norm_num)
    apply hne
    intro g hg
    have hmem : thetaH hMN ⟨g, hg⟩ ∈ innAut (L ⧸ center L) := hle ⟨⟨g, hg⟩, rfl⟩
    have h2 := (normalizerAction_mem_range_conj_iff h.standard.1.1
      (Subgroup.inclusion hMN ⟨g, hg⟩)).1 hmem
    rw [← h.centralizer_inf_sup_centralizer_eq hS hz hz2]
    exact ⟨hg, h2⟩
  have h1 := Subgroup.relIndex_mul_index hinnR
  rcases (Nat.dvd_prime Nat.prime_two).1 hout with h3 | h3
  · have htop : innAut (L ⧸ center L) = ⊤ := Subgroup.index_eq_one.1 h3
    have : R = ⊤ := eq_top_iff.2 (htop ▸ hinnR)
    exact MonoidHom.range_eq_top.1 this
  · rw [h3] at h1
    have hne1 : (innAut (L ⧸ center L)).relIndex R ≠ 1 := fun h4 =>
      hnle (Subgroup.relIndex_eq_one.1 h4)
    have hd : (innAut (L ⧸ center L)).relIndex R ∣ 2 := ⟨R.index, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h4 | h4
    · exact absurd h4 hne1
    · rw [h4] at h1
      have h5 : R.index = 1 := by omega
      exact MonoidHom.range_eq_top.1 (Subgroup.index_eq_one.1 h5)

theorem exists_outerConfig_facts [Finite G] (h : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) (hZ : center L = ⊥)
    (hcZ : center (L ⧸ center L) = ⊥) (hAF : AutSylowFacts (L ⧸ center L))
    (hout : (innAut (L ⧸ center L)).index ∣ 2) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2)
    (hrel : (L ⊔ zpowers z).relIndex (centralizer ({z} : Set G)) = 2) :
    ∃ (T₁ : Sylow 2 (centralizer ({z} : Set G))) (t : G) (tb : L ⧸ center L)
      (F : Subgroup (L ⧸ center L)),
      OuterConfig G L z t ((T₁ : Subgroup (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype) ∧
      (∃ t' : L, (t' : L ⧸ center L) = tb ∧ (t' : G) = t) ∧
      SylowWitness (L ⧸ center L) ((T₁ : Subgroup (centralizer ({z} : Set G))).map
        (thetaH (h.centralizer_le_normalizer hz hz2))) tb F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2' : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun e => by rw [e, orderOf_one] at hz2; omega
  have hMN := h.centralizer_le_normalizer hz hz2
  have hdisj : Disjoint L (zpowers z) :=
    disjoint_of_le_centralizer_of_center_eq_bot (zpowers_le.2 hz) hZ
  have hzH : z ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 rfl
  let zM : centralizer ({z} : Set G) := ⟨z, hzH⟩
  have hzM2 : orderOf zM = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hPz : IsPGroup 2 (zpowers zM) := IsPGroup.of_card (by rw [Nat.card_zpowers, hzM2, pow_one])
  obtain ⟨T₁, hT₁⟩ := hPz.exists_le_sylow
  have hθsurj := thetaH_surjective_of_rel h hS hz hz2 hMN hout hrel
  have hker := thetaH_ker h hS hz hz2 hMN
  have hker_le : (thetaH hMN).ker ≤ (T₁ : Subgroup (centralizer ({z} : Set G))) := by
    rw [hker]; exact hT₁
  let S : Subgroup (MulAut (L ⧸ center L)) :=
    (T₁ : Subgroup (centralizer ({z} : Set G))).map (thetaH hMN)
  have hSp : IsPGroup 2 S := T₁.isPGroup'.map (thetaH hMN)
  have hSidx : ¬ 2 ∣ S.index := by
    have h1 : S.index = ((T₁ : Subgroup (centralizer ({z} : Set G))) ⊔ (thetaH hMN).ker).index *
        (thetaH hMN).range.index := Subgroup.index_map _ (thetaH hMN)
    rw [h1, sup_eq_left.2 hker_le, MonoidHom.range_eq_top.2 hθsurj, index_top, mul_one]
    exact T₁.not_dvd_index
  obtain ⟨tb, F, hW⟩ := hAF S hSp hSidx
  have ht2 := hW.sq
  have ht1 := hW.ne
  obtain ⟨gb, hg4⟩ := hW.fourth
  have htS := hW.mem
  have hcen := hW.center
  obtain ⟨t', rfl⟩ := QuotientGroup.mk_surjective tb
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective gb
  have hinj : ∀ a b : L, (a : L ⧸ center L) = (b : L ⧸ center L) → a = b := by
    intro a b hab
    rw [QuotientGroup.eq, hZ, mem_bot] at hab
    exact inv_mul_eq_one.1 hab
  have hconjinj := HypOne.conj_injective_of_center_eq_bot hcZ
  have htL : (t' : G) ∈ centralizer ({z} : Set G) := le_centralizer_singleton hz t'.2
  let tH : centralizer ({z} : Set G) := ⟨(t' : G), htL⟩
  have hθt : thetaH hMN tH = MulAut.conj (t' : L ⧸ center L) := thetaH_conj hMN hz t'
  have htT₁ : tH ∈ (T₁ : Subgroup (centralizer ({z} : Set G))) := by
    obtain ⟨y, hy, hyt⟩ := htS
    have hyt' : thetaH hMN y = thetaH hMN tH := by rw [hθt]; exact hyt
    have hk : y⁻¹ * tH ∈ (thetaH hMN).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyt', inv_mul_cancel]
    have := (T₁ : Subgroup (centralizer ({z} : Set G))).mul_mem hy (hker_le hk)
    simpa using this
  have hsubmem : ∀ y : centralizer ({z} : Set G), y ∈ (T₁ : Subgroup (centralizer ({z} : Set G))) →
      thetaH hMN y ∈ S := fun y hy => ⟨y, hy, rfl⟩
  have hnormL : ∀ (y : centralizer ({z} : Set G)) (a : L), (y : G) * a * (y : G)⁻¹ ∈ L := by
    intro y a
    exact (mem_normalizer_iff.1 (hMN y.2) a).1 a.2
  have hcomm_zt : (t' : G) * z = z * t' := mem_centralizer_iff.1 hz t' t'.2
  refine ⟨T₁, t', _, F, ?_, ⟨t', rfl, rfl⟩, hW⟩
  exact
  { z_sq := hz2'
    z_ne := hz1
    z_cent := hz
    disjoint := hdisj
    cent_le := hMN
    index_two := hrel
    T_le := Subgroup.map_subtype_le _
    T_pgroup := T₁.isPGroup'.map _
    T_max := by
      intro P hPH hP hTP x hx
      have hxH : x ∈ centralizer ({z} : Set G) := hPH hx
      have hP'p : IsPGroup 2 (P.subgroupOf (centralizer ({z} : Set G))) :=
        hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
      have hle : (T₁ : Subgroup (centralizer ({z} : Set G))) ≤
          P.subgroupOf (centralizer ({z} : Set G)) := by
        intro y hy
        exact mem_subgroupOf.2 (hTP ⟨y, hy, rfl⟩)
      have heq := T₁.is_maximal' hP'p hle
      have hxP' : (⟨x, hxH⟩ : centralizer ({z} : Set G)) ∈
          P.subgroupOf (centralizer ({z} : Set G)) := mem_subgroupOf.2 hx
      rw [heq] at hxP'
      exact ⟨⟨x, hxH⟩, hxP', rfl⟩
    z_mem := ⟨zM, hT₁ (mem_zpowers zM), rfl⟩
    t_sq := by
      have h1 : ((t' * t' : L) : L ⧸ center L) = ((1 : L) : L ⧸ center L) := by
        simpa [QuotientGroup.mk_mul] using ht2
      have := hinj _ _ h1
      simpa using congrArg Subtype.val this
    t_ne := fun e => ht1 (by rw [show t' = 1 from Subtype.ext e]; rfl)
    t_mem_A := t'.2
    t_mem_T := ⟨tH, htT₁, rfl⟩
    t_central := by
      rintro y ⟨yH, hyH, rfl⟩
      have hyS : thetaH hMN yH ∈ S := hsubmem yH hyH
      have hc := ((hcen _ htS).2 (Or.inr rfl)) _ hyS
      have h1 : MulAut.conj (thetaH hMN yH (t' : L ⧸ center L)) =
          MulAut.conj (t' : L ⧸ center L) := by
        have h0 : thetaH hMN yH * MulAut.conj (t' : L ⧸ center L) * (thetaH hMN yH)⁻¹ =
            MulAut.conj (thetaH hMN yH (t' : L ⧸ center L)) := by
          ext x
          simp [MulAut.conj_apply]
        rw [← h0, hc]
        group
      have h2 := hconjinj h1
      have h3 : thetaH hMN yH (t' : L ⧸ center L) =
          ((⟨(yH : G) * t' * (yH : G)⁻¹, hnormL yH t'⟩ : L) : L ⧸ center L) :=
        thetaH_apply hMN yH t' _ rfl
      rw [h3] at h2
      have h5 : (yH : G) * t' * (yH : G)⁻¹ = t' := congrArg Subtype.val (hinj _ _ h2)
      show (yH : G) * t' = t' * yH
      calc (yH : G) * t' = ((yH : G) * t' * (yH : G)⁻¹) * yH := by group
        _ = t' * yH := by rw [h5]
    t_fourth := by
      refine ⟨(g' : G), g'.2, ?_⟩
      have h1 : ((g' * g' * (g' * g') : L) : L ⧸ center L) = ((t' : L) : L ⧸ center L) := by
        simpa [QuotientGroup.mk_mul] using hg4
      have := hinj _ _ h1
      simpa using congrArg Subtype.val this
    center_T := by
      rintro y ⟨yH, hyH, rfl⟩ hc
      have hyS : thetaH hMN yH ∈ S := hsubmem yH hyH
      have hcentral : ∀ β ∈ S, β * thetaH hMN yH = thetaH hMN yH * β := by
        rintro _ ⟨xH, hxH, rfl⟩
        have h6 : xH * yH = yH * xH := Subtype.ext (hc (xH : G) ⟨xH, hxH, rfl⟩)
        rw [← map_mul, ← map_mul, h6]
      rcases (hcen _ hyS).1 hcentral with h1 | h1
      · have hy : yH ∈ (thetaH hMN).ker := h1
        rw [hker] at hy
        have hyz : (yH : G) ∈ zpowers z := by
          obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hy
          exact ⟨n, by simpa using congrArg Subtype.val hn⟩
        rcases mem_zpowers_sq_eq_one hz2' hyz with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · have hy : tH⁻¹ * yH ∈ (thetaH hMN).ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hθt, h1, inv_mul_cancel]
        rw [hker] at hy
        have hyz : ((tH⁻¹ * yH : centralizer ({z} : Set G)) : G) ∈ zpowers z := by
          obtain ⟨n, hn⟩ := mem_zpowers_iff.1 hy
          exact ⟨n, by simpa using congrArg Subtype.val hn⟩
        have hval : ((tH⁻¹ * yH : centralizer ({z} : Set G)) : G) = (t' : G)⁻¹ * (yH : G) := rfl
        rw [hval] at hyz
        rcases mem_zpowers_sq_eq_one hz2' hyz with e | e
        · exact Or.inr (Or.inr (Or.inl (inv_mul_eq_one.1 e).symm))
        · refine Or.inr (Or.inr (Or.inr ?_))
          calc (yH : G) = t' * ((t' : G)⁻¹ * yH) := by group
            _ = t' * z := by rw [e]
            _ = z * t' := hcomm_zt }

end CFSG.EvenSporadicStandard.M22Std
