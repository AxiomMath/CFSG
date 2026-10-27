module

public import CFSG.Goldschmidt.StatementsX
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum
import CFSG.Goldschmidt.Steps.LemmaXBasic
import CFSG.Goldschmidt.Steps.LemmaXCore
import CFSG.Goldschmidt.Steps.Fusion
import CFSG.Goldschmidt.Steps.PropHSetup
import CFSG.Goldschmidt.Steps.ZStarLemma
import CFSG.LocalAnalysis.ShultStronglyClosedTI.NoLeastLocalFailure

public section

namespace CFSG.Goldschmidt

open CFSG.Open

namespace LemmaX

variable {G : Type} [Group G] [Finite G]

theorem four_le_card [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    {U : Subgroup G} (hUS : U ≤ S) (hU1 : U ≠ ⊥) (hsq : ∀ x ∈ U, x ^ 2 = 1)
    (hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G)) : 4 ≤ Nat.card U := by
  have hUp : IsPGroup 2 U := (S.isPGroup').to_le hUS
  by_contra h4
  obtain ⟨n, hn⟩ := hUp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hU1 (Subgroup.card_eq_one.1 (by simpa using hn))
  have hn1 : n = 1 := by
    by_contra hn1
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hU2 : Nat.card U = 2 := by rw [hn, hn1, pow_one]
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
  have heq : ∀ y : U, y ≠ 1 → y = u := fun y hy =>
    ((Nat.card_eq_two_iff' (1 : U)).1 hU2).unique hy hu1
  have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
  have hu2 : (u : G) * u = 1 := by rw [← sq]; exact hsq u u.2
  have hwc : ∀ g : G, g⁻¹ * (u : G) * g ∈ (S : Subgroup G) → g⁻¹ * (u : G) * g = u := by
    intro g hg
    have hmem : g⁻¹ * (u : G) * g ∈ U := hUcl u u.2 g hg
    have hne : (⟨_, hmem⟩ : U) ≠ 1 := by
      intro h
      apply hu1'
      have h' : g⁻¹ * (u : G) * g = 1 := congrArg Subtype.val h
      calc (u : G) = g * (g⁻¹ * u * g) * g⁻¹ := by group
        _ = 1 := by rw [h']; group
    exact congrArg Subtype.val (heq _ hne)
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar G u hu1' hu2
    (conj_eq_of_commute_of_weakClosure S hu2 hwc)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN0 | hNtop
  · have hz : (u : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := hN g
      rw [hN0, Subgroup.mem_bot] at h
      calc g * (u : G) = (g * u * g⁻¹ * (u : G)⁻¹) * u * g := by group
        _ = u * g := by rw [h, one_mul]
    rw [PropHSetup.center_eq_bot hnab, Subgroup.mem_bot] at hz
    exact hu1' hz
  · rw [hNtop, Subgroup.card_top] at hNodd
    have huo : orderOf (u : G) = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1'
    have h2 : 2 ∣ Nat.card G := huo ▸ orderOf_dvd_natCard (u : G)
    exact (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)

theorem normalizer_le_of_le (S : Sylow 2 G) {A U H E : Subgroup G} (hAS : A ≤ S)
    (hAab : IsMulCommutative A) (hAcl : fusionStronglyClosed (A : Set G) (S : Subgroup G))
    (hUS : U ≤ S) (hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G)) (hUA : U ≤ A)
    (hNH : Subgroup.normalizer (U : Set G) ≤ H)
    (hCH : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H) (hEU : E ≤ U)
    (hE1 : E ≠ ⊥) : Subgroup.normalizer (E : Set G) ≤ H := by
  intro g hg
  have hNA : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    N3a G S U A hUS hUcl ((S.isPGroup').to_le hAS) hUA
  have hmap : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ S := by
    intro y hy
    rw [mem_map_conj_inv_iff] at hy
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) (g * y * g⁻¹)).1 hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [e] at h1
    exact hUS (hEU h1)
  obtain ⟨n, hnN, hn⟩ := N4b G S A E g hAS hAab hAcl (hEU.trans hUS) hmap
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE1
  have hgn : g * n⁻¹ ∈ Subgroup.centralizer ({(e : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hn e e.2
    calc g * n⁻¹ * e = g * (n⁻¹ * e * n) * n⁻¹ := by group
      _ = g * (g⁻¹ * e * g) * n⁻¹ := by rw [h1]
      _ = e * (g * n⁻¹) := by group
  have h2 := hCH e (hEU e.2) (fun h => he1 (Subtype.ext h)) hgn
  have e' : g = g * n⁻¹ * n := by group
  rw [e']
  exact H.mul_mem h2 (hNH (hNA hnN))

theorem local_clause [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hIH : IH (Nat.card G)) (S : Sylow 2 G) {A U H : Subgroup G} (hAS : A ≤ S)
    (hAab : IsMulCommutative A) (hAcl : fusionStronglyClosed (A : Set G) (S : Subgroup G))
    (hUA : U ≤ A) (hUel : IsElemAbelian 2 U)
    (hUcl : fusionStronglyClosed (U : Set G) (S : Subgroup G))
    (hNH : Subgroup.normalizer (U : Set G) ≤ H)
    (hCH : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H) {t z : G}
    (ht : orderOf t = 2)
    (hSyl : fusionIsSylowIn 2 ((S : Subgroup G) ⊓ Subgroup.centralizer ({t} : Set G))
      (Subgroup.centralizer ({t} : Set G)))
    (hE4 : 4 ≤ Nat.card (U ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G))
    (hzU : z ∈ U) (hz1 : z ≠ 1) (htz : Commute t z)
    (htH : ¬ Subgroup.centralizer ({t} : Set G) ≤ H) :
    fusionStronglyEmbedded
      (H.subgroupOf (CFSG.ShultStronglyClosedTI.localInvolutionPointHull z t)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set G) with hCdef
  set L := CFSG.ShultStronglyClosedTI.localInvolutionPointHull z t with hLdef
  have hUS : U ≤ S := hUA.trans hAS
  have hLC : L ≤ C := CFSG.ShultStronglyClosedTI.localInvolutionPointHull_le_centralizer z t
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 htz.eq.symm
  obtain ⟨T, hT⟩ : ∃ T : Sylow 2 C, (T : Subgroup C) = ((S : Subgroup G) ⊓ C).subgroupOf C := by
    obtain ⟨hle, hp, hmax⟩ := hSyl
    refine ⟨⟨((S : Subgroup G) ⊓ C).subgroupOf C, hp.comap_subtype, fun {Q} hQ hTQ => ?_⟩, rfl⟩
    have h1 := hmax (Q.map C.subtype) (Subgroup.map_subtype_le Q) (hQ.map C.subtype) fun s hs =>
      ⟨⟨s, hle hs⟩, hTQ (show (⟨s, hle hs⟩ : C) ∈ ((S : Subgroup G) ⊓ C).subgroupOf C from hs),
        rfl⟩
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective Q).symm
  set E : Subgroup C := (U ⊓ C).subgroupOf C with hEdef
  have hE1 : U ⊓ C ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE4
    omega
  have hET : E ≤ (T : Subgroup C) := by
    rw [hT]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.2 ⟨hUS (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩
  have hEab : IsMulCommutative E :=
    isMulCommutative_subgroupOf (PropHSetup.isMulCommutative_of_le hUel.1 inf_le_left) C
  have hEexp : ∀ e ∈ E, e ^ 2 = 1 := fun e he =>
    Subtype.ext (by simpa using hUel.2 _ (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 he)).1)
  have hE4' : 4 ≤ Nat.card E := by
    rw [hEdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : U ⊓ C ≤ C)).toEquiv]
    exact hE4
  have hEcl : fusionStronglyClosed (E : Set C) (T : Subgroup C) := by
    intro a ha g hg
    rw [hT, Subgroup.mem_subgroupOf] at hg
    have ha' : (a : G) ∈ U ⊓ C := Subgroup.mem_subgroupOf.1 ha
    show g⁻¹ * a * g ∈ E
    rw [hEdef, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.2 ⟨?_, (g⁻¹ * a * g).2⟩
    have h1 : (g : G)⁻¹ * a * g ∈ (S : Subgroup G) := by
      simpa using (Subgroup.mem_inf.1 hg).1
    simpa using hUcl (a : G) (Subgroup.mem_inf.1 ha').1 (g : G) h1
  have hNJ : Subgroup.normalizer (E : Set C) ≤ H.subgroupOf C := by
    intro c hc
    rw [Subgroup.mem_subgroupOf]
    apply normalizer_le_of_le S hAS hAab hAcl hUS hUcl hUA hNH hCH inf_le_left hE1
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hxC : x ∈ C := (Subgroup.mem_inf.1 hx).2
      have := (Subgroup.mem_normalizer_iff.1 hc ⟨x, hxC⟩).1 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hx
      have hxC : x ∈ C := by
        have h1 : (c : G) * x * (c : G)⁻¹ ∈ C := (Subgroup.mem_inf.1 hx).2
        have e : x = (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * c := by group
        rw [e]
        exact C.mul_mem (C.mul_mem (C.inv_mem c.2) h1) c.2
      have := (Subgroup.mem_normalizer_iff.1 hc ⟨x, hxC⟩).2 (Subgroup.mem_subgroupOf.2 hx)
      exact Subgroup.mem_subgroupOf.1 this
  have hCJ : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set C) ≤ H.subgroupOf C := by
    intro e he he1 c hc
    rw [Subgroup.mem_subgroupOf]
    apply hCH (e : G) (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 he)).1
      (fun h => he1 (Subtype.ext h))
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    exact congrArg Subtype.val hc
  have hJ : H.subgroupOf C ≠ ⊤ := by
    intro htop
    apply htH
    intro c hc
    have : (⟨c, hc⟩ : C) ∈ H.subgroupOf C := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  have hCne : C ≠ ⊤ := by
    intro htop
    have htZ : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ C := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
    rw [PropHSetup.center_eq_bot hnab, Subgroup.mem_bot] at htZ
    rw [htZ, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hCcard : Nat.card C < Nat.card G := by
    rw [← Subgroup.card_top (G := G)]
    exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hCne)
  have hLconj : ∀ c ∈ C, ∀ x ∈ L, c * x * c⁻¹ ∈ L := by
    intro c hc x hx
    have hmap : L.map (MulAut.conj c).toMonoidHom ≤ L := by
      rw [hLdef, CFSG.ShultStronglyClosedTI.localInvolutionPointHull, MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨y, ⟨⟨g, rfl⟩, hyC⟩, rfl⟩
      refine ⟨⟨g * c⁻¹, ?_⟩, ?_⟩
      · show (g * c⁻¹)⁻¹ * z * (g * c⁻¹) = c * (g⁻¹ * z * g) * c⁻¹
        group
      · show c * (g⁻¹ * z * g) * c⁻¹ ∈ C
        exact C.mul_mem (C.mul_mem hc hyC) (C.inv_mem hc)
    exact hmap ⟨x, hx, rfl⟩
  have hιn : (Subgroup.inclusion hLC).range.Normal := by
    constructor
    rintro _ ⟨x, rfl⟩ c
    refine ⟨⟨(c : G) * x * (c : G)⁻¹, hLconj c c.2 x x.2⟩, ?_⟩
    apply Subtype.ext
    simp
  have hLnc : L ≤ (Subgroup.normalClosure (E : Set C)).map C.subtype := by
    rw [hLdef, CFSG.ShultStronglyClosedTI.localInvolutionPointHull, Subgroup.closure_le]
    rintro y ⟨⟨g, hg⟩, hyC⟩
    have hy : y = g⁻¹ * z * g := hg.symm
    refine ⟨⟨y, hyC⟩, ?_, rfl⟩
    have hy2 : (⟨y, hyC⟩ : C) ^ 2 ^ 1 = 1 := by
      apply Subtype.ext
      show y ^ 2 ^ 1 = 1
      rw [pow_one, sq, hy]
      calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
        _ = 1 := by rw [← sq, hUel.2 z hzU]; group
    obtain ⟨c, hc⟩ := exists_conj_mem_sylow T hy2
    rw [hT, Subgroup.mem_subgroupOf] at hc
    have e : ((c * ⟨y, hyC⟩ * c⁻¹ : C) : G) = (g * (c : G)⁻¹)⁻¹ * z * (g * (c : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hy]
      group
    have hcS : (g * (c : G)⁻¹)⁻¹ * z * (g * (c : G)⁻¹) ∈ (S : Subgroup G) := by
      rw [← e]
      exact (Subgroup.mem_inf.1 hc).1
    have hmem : c * ⟨y, hyC⟩ * c⁻¹ ∈ E := by
      rw [hEdef, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.2 ⟨?_, (c * ⟨y, hyC⟩ * c⁻¹).2⟩
      rw [e]
      exact hUcl z hzU _ hcS
    have h1 := (Subgroup.normalClosure_normal (s := (E : Set C))).conj_mem _
      (Subgroup.subset_normalClosure hmem) c⁻¹
    have e2 : c⁻¹ * (c * ⟨y, hyC⟩ * c⁻¹) * c⁻¹⁻¹ = (⟨y, hyC⟩ : C) := by group
    rwa [e2] at h1
  have hιE : (Subgroup.inclusion hLC).range ≤ Subgroup.normalClosure (E : Set C) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨w, hw, hwx⟩ := hLnc x.2
    have : w = Subgroup.inclusion hLC x := Subtype.ext hwx
    rw [← this]
    exact hw
  have hzL : z ∈ L := CFSG.ShultStronglyClosedTI.distinguished_mem_localInvolutionPointHull htz
  have hιe : ∃ x : L, Subgroup.inclusion hLC x ∈ E ∧ Subgroup.inclusion hLC x ≠ 1 := by
    refine ⟨⟨z, hzL⟩, ?_, ?_⟩
    · rw [hEdef, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.2 ⟨hzU, hzC⟩
    · intro h
      exact hz1 (congrArg Subtype.val h)
  have hres := core_embedding hIH hCcard T hET hEab hEexp hE4' hEcl hNJ hCJ hJ
    (Subgroup.inclusion hLC) (Subgroup.inclusion_injective hLC) hιn hιE hιe
  have heq : (H.subgroupOf C).comap (Subgroup.inclusion hLC) = H.subgroupOf L := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [← heq]
  exact hres

end LemmaX

open LemmaX in
theorem lemmaX :
    S_lemmaX := by
  intro G _ _ _ hnab hIH S A U hAS hAab hAcl hUA hUel hU1 hUcl hrk H hHtop hNH hCH
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUS : U ≤ S := hUA.trans hAS
  have hU4 : 4 ≤ Nat.card U := four_le_card hnab S hUS hU1 hUel.2 hUcl
  have hNA : Subgroup.normalizer (A : Set G) ≤ H :=
    (N3a G S U A hUS hUcl ((S.isPGroup').to_le hAS) hUA).trans hNH
  obtain ⟨z, hzU, hz1, hzS⟩ : ∃ z ∈ U, z ≠ 1 ∧ ∀ s ∈ (S : Subgroup G), s * z = z * s := by
    have : Group.IsNilpotent (S : Subgroup G) := S.isPGroup'.isNilpotent
    have hn : (U.subgroupOf S).Normal := normal_subgroupOf_of_stronglyClosed hUS hUcl
    have hne : U.subgroupOf S ≠ ⊥ := by
      intro h
      apply hU1
      rw [eq_bot_iff]
      intro u hu
      have : (⟨u, hUS hu⟩ : (S : Subgroup G)) ∈ U.subgroupOf S := hu
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    obtain ⟨x, hx1⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    obtain ⟨hxU, hxZ⟩ := Subgroup.mem_inf.1 x.2
    refine ⟨((x : (S : Subgroup G)) : G), hxU, ?_, fun s hs => ?_⟩
    · intro h
      exact hx1 (Subtype.ext (Subtype.ext h))
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hxZ ⟨s, hs⟩)
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hUel.2 z hzU) hz1
  have hzsq : z ^ 2 ^ 1 = 1 := by rw [pow_one]; exact hUel.2 z hzU
  have hzH : z ∈ H := hNH (Subgroup.le_normalizer hzU)
  have hcen : CFSG.ShultStronglyClosedTI.InvolutionPointCentralSylow z :=
    ⟨S, hUS hzU, Subgroup.mem_center_iff.2 fun s => Subtype.ext (hzS s s.2)⟩
  have hloc : ∀ t : G, orderOf t = 2 → Commute t z →
      ¬ Subgroup.centralizer ({t} : Set G) ≤ H →
      fusionStronglyEmbedded
        (H.subgroupOf (CFSG.ShultStronglyClosedTI.localInvolutionPointHull z t)) := by
    intro t ht htz htH
    set C := Subgroup.centralizer ({t} : Set G) with hCdef
    have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 htz.eq.symm
    have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
    have htsq : t ^ 2 ^ 1 = 1 := by rw [pow_one, ← ht, pow_orderOf_eq_one]
    obtain ⟨T₀, hT₀⟩ := (isPGroup_zpowers_of_pow_eq_one
      (t := (⟨z, hzC⟩ : C)) (n := 1) (Subtype.ext hzsq)).exists_le_sylow
    have hzT₀ : (⟨z, hzC⟩ : C) ∈ (T₀ : Subgroup C) := hT₀ (Subgroup.mem_zpowers _)
    have htT₀ : (⟨t, htC⟩ : C) ∈ (T₀ : Subgroup C) := by
      have hcent : Subgroup.zpowers (⟨t, htC⟩ : C) ≤ Subgroup.center C := by
        rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
        intro c
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
      have := Subgroup.normal_of_le_center hcent
      exact (isPGroup_zpowers_of_pow_eq_one (Subtype.ext htsq)).le_sylow_of_normal T₀
        (Subgroup.mem_zpowers _)
    obtain ⟨S', hS'⟩ := (T₀.isPGroup'.map C.subtype).exists_le_sylow
    have hzS' : z ∈ (S' : Subgroup G) := hS' ⟨_, hzT₀, rfl⟩
    have htS' : t ∈ (S' : Subgroup G) := hS' ⟨_, htT₀, rfl⟩
    have hSyl : fusionIsSylowIn 2 ((S' : Subgroup G) ⊓ C) C := by
      refine ⟨inf_le_right, S'.isPGroup'.to_le inf_le_left, fun P hPC hP hSP => ?_⟩
      have hT₀P : (T₀ : Subgroup C) ≤ P.subgroupOf C := by
        intro x hx
        rw [Subgroup.mem_subgroupOf]
        exact hSP (Subgroup.mem_inf.2 ⟨hS' ⟨x, hx, rfl⟩, x.2⟩)
      have hPeq := T₀.is_maximal' hP.comap_subtype hT₀P
      refine le_antisymm (fun x hxP => ?_) hSP
      have hx : (⟨x, hPC hxP⟩ : C) ∈ (T₀ : Subgroup C) := by
        rw [← hPeq]
        exact hxP
      exact Subgroup.mem_inf.2 ⟨hS' ⟨_, hx, rfl⟩, hPC hxP⟩
    obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G S S'
    have hS'eq : (S' : Subgroup G) = (S : Subgroup G).map (MulAut.conj k).toMonoidHom := by
      rw [← hk]
      rfl
    have hzk : k⁻¹ * z * k ∈ U := by
      have h1 : z ∈ (S : Subgroup G).map (MulAut.conj k).toMonoidHom := hS'eq ▸ hzS'
      rw [mem_map_conj_iff] at h1
      exact hUcl z hzU k h1
    have hkH : k ∈ H := by
      obtain ⟨h, hhH, hh⟩ := N5a G S A H hAS hAab hAcl hNA z k hzH
        (hNH (Subgroup.le_normalizer hzk)) ⟨1, hzsq⟩
      have h1 : k * h⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc k * h⁻¹ * z = k * (h⁻¹ * z * h) * h⁻¹ := by group
          _ = k * (k⁻¹ * z * k) * h⁻¹ := by rw [hh]
          _ = z * (k * h⁻¹) := by group
      have h2 := H.mul_mem (hCH z hzU hz1 h1) hhH
      simpa using h2
    set A' := A.map (MulAut.conj k).toMonoidHom with hA'
    set U' := U.map (MulAut.conj k).toMonoidHom with hU'
    have hA'S : A' ≤ S' := by
      rw [hS'eq]
      exact Subgroup.map_mono hAS
    have hU'S : U' ≤ S' := by
      rw [hS'eq]
      exact Subgroup.map_mono hUS
    have hA'cl : fusionStronglyClosed (A' : Set G) (S' : Subgroup G) := by
      rw [hS'eq]
      exact stronglyClosed_map_conj hAcl k
    have hU'cl : fusionStronglyClosed (U' : Set G) (S' : Subgroup G) := by
      rw [hS'eq]
      exact stronglyClosed_map_conj hUcl k
    have hU'el : IsElemAbelian 2 U' := by
      refine ⟨isMulCommutative_map hUel.1 _, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      rw [← map_pow, hUel.2 u hu, map_one]
    have hNH' : Subgroup.normalizer (U' : Set G) ≤ H := by
      intro g hg
      have h1 : k⁻¹ * g * k ∈ Subgroup.normalizer (U : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h2 := Subgroup.mem_normalizer_iff.1 hg (k * y * k⁻¹)
        rw [mem_map_conj_iff, mem_map_conj_iff] at h2
        have e1 : k⁻¹ * (k * y * k⁻¹) * k = y := by group
        have e2 : k⁻¹ * (g * (k * y * k⁻¹) * g⁻¹) * k =
            k⁻¹ * g * k * y * (k⁻¹ * g * k)⁻¹ := by group
        rw [e1, e2] at h2
        exact h2
      have e : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hkH (hNH h1)) (H.inv_mem hkH)
    have hCH' : ∀ u ∈ U', u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ H := by
      intro u hu hu1 g hg
      rw [mem_map_conj_iff] at hu
      have hu1' : k⁻¹ * u * k ≠ 1 := by
        intro h
        apply hu1
        calc u = k * (k⁻¹ * u * k) * k⁻¹ := by group
          _ = 1 := by rw [h]; group
      have h1 : k⁻¹ * g * k ∈ Subgroup.centralizer ({k⁻¹ * u * k} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
        calc k⁻¹ * g * k * (k⁻¹ * u * k) = k⁻¹ * (g * u) * k := by group
          _ = k⁻¹ * (u * g) * k := by rw [hg]
          _ = k⁻¹ * u * k * (k⁻¹ * g * k) := by group
      have h2 := hCH _ hu hu1' h1
      have e : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hkH h2) (H.inv_mem hkH)
    have hzU' : z ∈ U' := mem_map_conj_iff.2 hzk
    have hcardU' : Nat.card U' = Nat.card U :=
      Subgroup.card_map_of_injective (MulAut.conj k).injective
    have hE4 : 4 ≤ Nat.card (U' ⊓ C : Subgroup G) := by
      rcases hrk with h8 | hZS
      ·
        have htN : t ∈ Subgroup.normalizer (U' : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            have := conj_mem_of_stronglyClosed hU'S hU'cl ((S' : Subgroup G).inv_mem htS') hx
            simpa using this
          · intro hx
            have := conj_mem_of_stronglyClosed hU'S hU'cl htS' hx
            simpa [mul_assoc] using this
        have htt : t * t = 1 := by rw [← sq]; simpa using htsq
        have hsq := card_le_card_inf_centralizer_sq hU'el.1 hU'el.2 htN htt
        obtain ⟨m, hm⟩ := ((S'.isPGroup').to_le (inf_le_left.trans hU'S)).exists_card_eq
        rw [hcardU', hm] at hsq
        rw [hm]
        rcases Nat.lt_or_ge m 2 with hm2 | hm2
        · exfalso
          have h1 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          have h2 : (2 ^ m) ^ 2 ≤ 4 := by nlinarith
          omega
        · calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      ·
        have hU'C : U' ≤ C := by
          rintro _ ⟨u, hu, rfl⟩
          rw [Subgroup.mem_centralizer_singleton_iff]
          have hts : k⁻¹ * t * k ∈ (S : Subgroup G) := by
            have h1 : t ∈ (S : Subgroup G).map (MulAut.conj k).toMonoidHom := hS'eq ▸ htS'
            rwa [mem_map_conj_iff] at h1
          have hc := Subgroup.mem_centralizer_iff.1 (hZS hu) _ hts
          show k * u * k⁻¹ * t = t * (k * u * k⁻¹)
          calc k * u * k⁻¹ * t = k * (u * (k⁻¹ * t * k)) * k⁻¹ := by group
            _ = k * ((k⁻¹ * t * k) * u) * k⁻¹ := by rw [hc]
            _ = t * (k * u * k⁻¹) := by group
        rw [inf_of_le_left hU'C, hcardU']
        exact hU4
    exact local_clause hnab hIH S' hA'S (isMulCommutative_map hAab _) hA'cl
      (Subgroup.map_mono hUA) hU'el hU'cl hNH' hCH' ht hSyl hE4 hzU' hz1 htz htH
  have hcrit := CFSG.ShultStronglyClosedTI.local_criterion G H z
    ⟨hHtop, hzH, hz2, fun g => ?_, hloc⟩ hcen
  · have hhull : CFSG.ShultStronglyClosedTI.involutionPointHull z = ⊤ := by
      rw [CFSG.ShultStronglyClosedTI.minimalLocalFailure_hull_eq_normalClosure]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({z} : Set G))
          with h | h
      · exfalso
        apply hz1
        have : z ∈ Subgroup.normalClosure ({z} : Set G) := Subgroup.subset_normalClosure rfl
        rw [h, Subgroup.mem_bot] at this
        exact this
      · exact h
    rw [hhull] at hcrit
    rw [isStronglyEmbeddedOrder_iff]
    have hcomap : (H.subgroupOf ⊤).comap (Subgroup.topEquiv (G := G)).symm.toMonoidHom = H := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [← hcomap]
    refine fusionStronglyEmbedded_comap _ (MulEquiv.surjective _) ?_ hcrit
    rw [(MonoidHom.ker_eq_bot_iff _).2 (MulEquiv.injective _), Subgroup.card_bot]
    exact odd_one
  ·
    show z ∈ H.map (MulAut.conj g⁻¹).toMonoidHom ↔ g ∈ H
    rw [mem_map_conj_inv_iff]
    constructor
    · intro hg
      obtain ⟨h, hhH, hh⟩ := N5a G S A H hAS hAab hAcl hNA z g⁻¹ hzH (by simpa using hg)
        ⟨1, hzsq⟩
      have hhg : h * g ∈ Subgroup.centralizer ({z} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have e : g * z * g⁻¹ = h⁻¹ * z * h := by rw [hh]; group
        calc h * g * z = h * (g * z * g⁻¹) * g := by group
          _ = h * (h⁻¹ * z * h) * g := by rw [e]
          _ = z * (h * g) := by group
      have := H.mul_mem (H.inv_mem hhH) (hCH z hzU hz1 hhg)
      simpa using this
    · intro hg
      exact H.mul_mem (H.mul_mem hg hzH) (H.inv_mem hg)

end CFSG.Goldschmidt
