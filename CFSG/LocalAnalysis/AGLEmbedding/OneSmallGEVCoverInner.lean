module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVStarIa
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieDefs
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem mulAut_conj_comm {L : Type*} [Group L] (α : MulAut L) (e : L) (he : α e = e) :
    MulAut.conj e * α = α * MulAut.conj e := by
  apply MulEquiv.ext
  intro l
  change e * α l * e⁻¹ = α (e * l * e⁻¹)
  rw [map_mul, map_mul, map_inv, he]

theorem mem_inner_of_pRank_le_two {L : Type*} [Group L] [Finite L] {p : ℕ} [hp : Fact p.Prime]
    (hZ : Subgroup.center L = ⊥) (hsm : Open.pRank p (⊤ : Subgroup (MulAut L)) ≤ 2)
    {E : Subgroup L} (hE : Open.IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    {α : MulAut L} (hα : α ^ p = 1) (hαE : ∀ e ∈ E, α e = e) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L := by
  by_contra hα'
  have hα1 : α ≠ 1 := fun h => hα' (h ▸
    (CFSG.ComponentClassification.OuterAutomorphisms.inner L).one_mem)
  have hαp : orderOf α = p := orderOf_eq_prime hα hα1
  set A := Subgroup.zpowers α with hA
  have hcomm : ∀ (e : E) (a : A), Commute ((MulAut.conj.comp E.subtype) e) (A.subtype a) := by
    rintro e ⟨a, j, rfl⟩
    exact (show Commute (MulAut.conj (e : L)) α from mulAut_conj_comm α e (hαE e e.2)).zpow_right j
  set θ := MonoidHom.noncommCoprod (MulAut.conj.comp E.subtype) A.subtype hcomm with hθ
  have hθapp : ∀ x : E × A, θ x = MulAut.conj (x.1 : L) * (x.2 : MulAut L) := fun x => rfl
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨e, a⟩ h
    have h1 : MulAut.conj (e : L) * (a : MulAut L) = 1 := (hθapp _).symm.trans h
    have ha : (a : MulAut L) ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner L := by
      rw [eq_inv_of_mul_eq_one_right h1, ← map_inv]
      exact ⟨_, rfl⟩
    have ha1 : (a : MulAut L) = 1 := by
      by_contra hne
      apply hα'
      have hle : Subgroup.zpowers (a : MulAut L) ≤ A := Subgroup.zpowers_le.mpr a.2
      have hcard : Nat.card (Subgroup.zpowers (a : MulAut L)) = p := by
        have hdvd : Nat.card (Subgroup.zpowers (a : MulAut L)) ∣ p := by
          rw [← hαp, ← Nat.card_zpowers α]; exact Subgroup.card_dvd_of_le hle
        rcases (Nat.dvd_prime hp.out).mp hdvd with h2 | h2
        · exact absurd (Subgroup.card_eq_one.mp h2) fun h => hne (Subgroup.zpowers_eq_bot.mp h)
        · exact h2
      have heq : Subgroup.zpowers (a : MulAut L) = A :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, hαp])
      have hαa : α ∈ Subgroup.zpowers (a : MulAut L) := by rw [heq]; exact Subgroup.mem_zpowers α
      exact (Subgroup.zpowers_le.mpr ha) hαa
    rw [ha1, mul_one] at h1
    have he1 : (e : L) = 1 := by
      have hc : (e : L) ∈ Subgroup.center L := by
        rw [Subgroup.mem_center_iff]
        intro m
        have h3 := congrArg (fun f : MulAut L => f m) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h3
        calc m * (e : L) = (e : L) * m * (e : L)⁻¹ * (e : L) := by rw [h3]
          _ = (e : L) * m := by group
      rw [hZ, Subgroup.mem_bot] at hc
      exact hc
    have ha2 : a = 1 := Subtype.ext ha1
    have he2 : e = 1 := Subtype.ext he1
    rw [ha2, he2, Subgroup.mem_bot]
    rfl
  have hEcomm := hE.1
  have hAc : ∀ a b : A, a * b = b * a := by
    rintro ⟨_, i, rfl⟩ ⟨_, j, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← zpow_add, ← zpow_add, add_comm]
  have hAp : ∀ a : A, a ^ p = 1 := by
    rintro ⟨_, i, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  have hFel : Open.IsElemAbelian p θ.range := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
      apply Subtype.ext
      change θ x * θ y = θ y * θ x
      rw [← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (hEcomm.is_comm.comm x.1 y.1) (hAc x.2 y.2)
    · rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have h1 : x ^ p = 1 := Prod.ext (Subtype.ext (hE.2 _ x.1.2)) (hAp x.2)
      rw [h1, map_one]
  have hFc : Nat.card θ.range = p ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_prod, hEc,
      Nat.card_zpowers, hαp]
    ring
  have h3 := CFSG.SectionRank.le_pRank hp.out.one_lt le_top hFel hFc
  omega

theorem ne_bot_of_commutator_eq_self {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {T : Subgroup X} (hT : IsPGroup p T) (hc : ⁅T, T⁆ = T) : T = ⊥ := by
  by_contra hne
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hne
  have : Group.IsPerfect T := Subgroup.isPerfect_iff.mpr hc
  have : Group.IsNilpotent T := hT.isNilpotent
  exact Group.IsPerfect.not_isSolvable T inferInstance

theorem D1CompI.mem_sup_centralizer_of_comm (hK1 : KFactOneLie)
    (hU : KFactUnitarySylowStructure) {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G}
    {M Hs R : Subgroup G} {Rbars : Sylow p (Hs ⧸ primeComplementCore (G := Hs) p)}
    {Ks : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)}
    (hds : D1CompI p P M Hs R Rbars Ks) {x : Hs ⧸ primeComplementCore (G := Hs) p}
    (hxc : ∀ r ∈ (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)), x * r = r * x)
    (hxp : x ^ p = 1) : x ∈ Ks ⊔ Subgroup.centralizer (Ks : Set _) := by
  have hp := hds.cfg.red.prime
  have hp2 := hds.cfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hKn : Ks.Normal := hds.cfg.red.normal_of_rankOne hds.comp hds.noncyclic
  set α : MulAut Ks := MulAut.conjNormal x with hα
  have hαp : α ^ p = 1 := by rw [hα, ← map_pow, hxp, map_one]
  obtain ⟨T₁, hT₁, hs, hn, hc, hTnc, hΓT⟩ := hds.exists_sylow
  have hαT : ∀ t ∈ (T₁ : Subgroup Ks), α t = t := by
    intro t ht
    apply Subtype.ext
    have htR : (t : Hs ⧸ primeComplementCore (G := Hs) p) ∈
        (Rbars : Subgroup (Hs ⧸ primeComplementCore (G := Hs) p)) ⊓ Ks := hT₁ ▸ ⟨t, ht, rfl⟩
    rw [hα, MulAut.conjNormal_apply]
    calc x * t * x⁻¹ = t * x * x⁻¹ := by rw [hxc t htR.1]
      _ = t := by group
  have hinn : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner Ks := by
    by_cases hsm : Open.pRank p (⊤ : Subgroup (MulAut Ks)) ≤ 2
    · have : Fact (IsPGroup p (T₁ : Subgroup Ks)) := ⟨T₁.isPGroup'⟩
      obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := (T₁ : Subgroup Ks)) hp2 hTnc
      set E := S.map (T₁ : Subgroup Ks).subtype with hE
      have hEl : CFSG.IsElementaryAbelian p E := hSel.map _
      have hEel : Open.IsElemAbelian p E :=
        ⟨hEl.toIsMulCommutative, fun y hy => CFSG.elemPow_eq_one_of_isElementaryAbelian y hy⟩
      have hEc : Nat.card E = p ^ 2 := by
        rw [hE, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hScard]
      exact mem_inner_of_pRank_le_two hds.center hsm hEel hEc hαp fun e he => by
        obtain ⟨s, -, rfl⟩ := he
        exact hαT _ s.2
    · have hF := hK1 Ks hs hn hc p hp hp2 T₁ hTnc hΓT hsm
      have hne : (T₁ : Subgroup Ks) ≠ ⊥ := fun h => hTnc (h ▸ inferInstance)
      rcases hF.centralizer (T₁ : Subgroup Ks) le_rfl hne le_rfl with h | ⟨hZT, hUn⟩
      · obtain ⟨t, -, ht⟩ := h α hαT
        exact ⟨t, ht.symm⟩
      · exfalso
        obtain ⟨d, hd, ⟨e⟩⟩ := hUn
        obtain ⟨-, hcomm, -⟩ := hU Ks p d hp2 hd ⟨e⟩ T₁
        have hcc : ⁅(T₁ : Subgroup Ks), (T₁ : Subgroup Ks)⁆ = (T₁ : Subgroup Ks) := by
          rw [hcomm]
          exact hZT.symm
        exact hne (ne_bot_of_commutator_eq_self T₁.isPGroup' hcc)
  obtain ⟨k, hk⟩ := hinn
  rw [hα] at hk
  have hcen : (k : Hs ⧸ primeComplementCore (G := Hs) p)⁻¹ * x ∈
      Subgroup.centralizer (Ks : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := congrArg
      (fun f : MulAut Ks => ((f ⟨y, hy⟩ : Ks) : Hs ⧸ primeComplementCore (G := Hs) p)) hk
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    calc y * ((k : Hs ⧸ primeComplementCore (G := Hs) p)⁻¹ * x) =
        (k : Hs ⧸ primeComplementCore (G := Hs) p)⁻¹ *
          (k * y * (k : Hs ⧸ primeComplementCore (G := Hs) p)⁻¹) * x := by group
      _ = (k : Hs ⧸ primeComplementCore (G := Hs) p)⁻¹ * (x * y * x⁻¹) * x := by rw [h]
      _ = (k : Hs ⧸ primeComplementCore (G := Hs) p)⁻¹ * x * y := by group
  have e : x = (k : Hs ⧸ primeComplementCore (G := Hs) p) *
      ((k : Hs ⧸ primeComplementCore (G := Hs) p)⁻¹ * x) := by group
  rw [e]
  exact Subgroup.mul_mem_sup k.2 hcen

end CFSG.AGLEmbedding
