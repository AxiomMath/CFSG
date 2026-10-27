module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwOrbGS3
public import Certificates.Certificate22802
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4End43H
import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Facts
public import Certificates.Kernel.ThCent.Leaves
import CFSG.Goldschmidt75.WeakClosure

public section

namespace CFSG.ComponentClassification.GrSLit.KSwOrb

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G]

theorem q8_facts {Q : Subgroup G} (e : ↥Q ≃* QuaternionGroup 2) {y : G} (hy : y ∈ Q)
    (hy2 : y * y ≠ 1) :
    y * y * (y * y) = 1 ∧ (∀ w ∈ Q, w ≠ 1 → w = y * y ∨ w * w = y * y) ∧
      ∃ u ∈ Q, ∃ v ∈ Q, u * v ≠ v * u := by
  have k1 : ∀ u : QuaternionGroup 2, u * u ≠ 1 → u * u = QuaternionGroup.a 2 := by decide
  have k2 : ∀ u : QuaternionGroup 2, u ≠ 1 →
      u = QuaternionGroup.a 2 ∨ u * u = QuaternionGroup.a 2 := by decide
  have k3 : QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) := by decide
  have k4 : QuaternionGroup.a 1 * QuaternionGroup.xa 0 ≠
      QuaternionGroup.xa 0 * (QuaternionGroup.a 1 : QuaternionGroup 2) := by decide
  have hy' : e ⟨y, hy⟩ * e ⟨y, hy⟩ ≠ 1 := by
    rw [← map_mul, ne_eq, MulEquiv.map_eq_one_iff]
    exact fun h => hy2 (congrArg Subtype.val h)
  have hyc : e (⟨y, hy⟩ * ⟨y, hy⟩) = QuaternionGroup.a 2 := by
    rw [map_mul]
    exact k1 _ hy'
  refine ⟨?_, fun w hw hw1 => ?_, ?_⟩
  · have h1 : (⟨y, hy⟩ * ⟨y, hy⟩ * (⟨y, hy⟩ * ⟨y, hy⟩) : ↥Q) = 1 :=
      e.injective (by rw [map_mul, hyc, k3, map_one])
    exact congrArg Subtype.val h1
  · have hw' : e ⟨w, hw⟩ ≠ 1 := by
      rw [ne_eq, MulEquiv.map_eq_one_iff]
      exact fun h => hw1 (congrArg Subtype.val h)
    rcases k2 _ hw' with h | h
    · exact Or.inl (congrArg Subtype.val (e.injective (h.trans hyc.symm)))
    · exact Or.inr (congrArg Subtype.val
        (e.injective ((map_mul e ⟨w, hw⟩ ⟨w, hw⟩).trans (h.trans hyc.symm))))
  · refine ⟨(e.symm (QuaternionGroup.a 1) : G), (e.symm _).2,
      (e.symm (QuaternionGroup.xa 0) : G), (e.symm _).2, fun h => k4 ?_⟩
    have h' : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
        e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext h
    rw [← map_mul, ← map_mul] at h'
    exact e.symm.injective h'

theorem isPGroup_zpowers_of_four {u : G} (hu : u * u * (u * u) = 1) :
    IsPGroup 2 (zpowers u) := by
  have h4 : u ^ 2 ^ 2 = 1 := by
    rw [show u ^ 2 ^ 2 = u * u * (u * u) by
      rw [show (2 : ℕ) ^ 2 = 4 from rfl]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
    exact hu
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h4)
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

variable [Finite G]

theorem exists_conj_of_two_rank
    {a x : G}
    {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S)
    (hCM : centralizer ({a} : Set G) ≤ normalizer (W : Set G)) {g : G} {E : Subgroup G}
    (hEa : E ≤ centralizer ({a} : Set G)) (hE : IsEightGroup E)
    (hEb : ∀ e ∈ E, e * (g⁻¹ * a * g) = g⁻¹ * a * g * e) {s : G} (hsa : s * a = a * s)
    (hs2 : s * s = 1) (hsE : ∀ e ∈ E, s * e = e * s) (hsn : s ∉ E)
    (hsb : s * (g⁻¹ * a * g) = g⁻¹ * a * g * s) :
    ∃ m ∈ normalizer (W : Set G), g⁻¹ * a * g = m⁻¹ * a * m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, hS, -, -⟩ := id hset
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  set b : G := g⁻¹ * a * g with hbdef
  obtain ⟨hF, -⟩ := GrS4.isElemTwo_sup_zpowers hE.1 hs2 hsn fun e he => (hsE e he).symm
  have hFa : E ⊔ zpowers s ≤ centralizer ({a} : Set G) :=
    sup_le hEa (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hsa))
  obtain ⟨c, hcC, hc⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn
    (GrS5S.isSylowTwoIn_centralizer hS2 hcent hSyl) hFa hF.isPGroup
  have hbc : (g * c)⁻¹ * a * (g * c) = c⁻¹ * b * c := by rw [hbdef]; group
  have hmemE' : ∀ e' ∈ E.map (MulAut.conj c⁻¹).toMonoidHom, ∃ e ∈ E, e' = c⁻¹ * e * c := by
    rintro _ ⟨e, he, rfl⟩
    exact ⟨e, he, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  have hE'S : E.map (MulAut.conj c⁻¹).toMonoidHom ≤ S := by
    intro e' he'
    obtain ⟨e, he, rfl⟩ := hmemE' e' he'
    exact hc e (mem_sup_left he)
  have hE' : IsEightGroup (E.map (MulAut.conj c⁻¹).toMonoidHom) :=
    ⟨hE.1.map_conj _, by rw [card_map_of_injective (MulAut.conj c⁻¹).injective, hE.2]⟩
  obtain ⟨m, hm, hbm⟩ := GrS5S.exists_conj_of_not_isolated hset hcent hWB hSyl (g := g * c)
    hE'S hE' (fun e' he' => by
      obtain ⟨e, he, rfl⟩ := hmemE' e' he'
      rw [hbc, show c⁻¹ * e * c * (c⁻¹ * b * c) = c⁻¹ * (e * b) * c by group, hEb e he]
      group) (hc s (mem_sup_right (mem_zpowers s)))
    (by rw [show c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * (s * s) * c by group, hs2]; group)
    (fun e' he' => by
      obtain ⟨e, he, rfl⟩ := hmemE' e' he'
      rw [show c⁻¹ * s * c * (c⁻¹ * e * c) = c⁻¹ * (s * e) * c by group, hsE e he]
      group)
    (fun h => by
      obtain ⟨e, he, he'⟩ := hmemE' _ h
      have hse : s = e := mul_left_cancel (mul_right_cancel he')
      exact hsn (hse ▸ he))
    (by rw [hbc, show c⁻¹ * s * c * (c⁻¹ * b * c) = c⁻¹ * (s * b) * c by group, hsb]; group)
  refine ⟨m * c⁻¹, mul_mem hm (inv_mem (hCM hcC)), ?_⟩
  calc b = c * ((g * c)⁻¹ * a * (g * c)) * c⁻¹ := by rw [hbdef]; group
    _ = (m * c⁻¹)⁻¹ * a * (m * c⁻¹) := by rw [hbm]; group

theorem exists_unitary_conj
    {a x : G}
    {J S W : Subgroup G} (hset : L34Sec4Setting G a x J S) (hcent : ∀ s ∈ S, s * a = a * s)
    (h3 : IsThreeConnected (S ⊓ withKernel J)) (hZ1 : S ⊓ zStarIn J = ⊥)
    (hWB : ∀ B : Subgroup G, B ≤ S ⊓ withKernel J → IsAbelianTwoOfRank 3 B → wGroup B = W)
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G))
    (hSyl : ∃ P : Sylow 2 G, (P : Subgroup G) = S) {k : G} (hkS : k⁻¹ * a * k ∈ S)
    (hk : ¬ ∃ m ∈ normalizer (W : Set G), k⁻¹ * a * k = m⁻¹ * a * m) :
    k⁻¹ * a * k ∉ withKernel J ∧ ∃ c ∈ normalizer (J : Set G) ⊓ centralizer ({a} : Set G),
      c⁻¹ * (k⁻¹ * a * k) * c ∈ S ∧ IsL34Unitary J (c⁻¹ * (k⁻¹ * a * k) * c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, -, -⟩ := id hset
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have ha2 : orderOf a = 2 := hU3.1
  have haK : a ∈ coreActionKernel J := GrS4.mem_coreActionKernel_of_le_centralizer hJa
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hka : k⁻¹ * a * k ≠ a := fun h => hk ⟨1, one_mem _, by rw [h]; group⟩
  have hkK : k⁻¹ * a * k ∉ withKernel J := fun h =>
    hk (GrS5S.exists_conj_of_mem_withKernel hset hcent h3 hWB hNJ hSyl hkS h)
  refine ⟨hkK, ?_⟩
  obtain ⟨c, hc, E, hES, hE, hbE, haE, -, hE4⟩ := GrS5S.exists_eight_of_conj hset hcent hkS hka
  have hcN : c ∈ normalizer (J : Set G) := (mem_inf.mp hc).1
  have hkc : (k * c)⁻¹ * a * (k * c) = c⁻¹ * (k⁻¹ * a * k) * c := by group
  have hb'K : c⁻¹ * (k⁻¹ * a * k) * c ∉ withKernel J := by
    intro h
    apply hkK
    have := GrS4.map_conj_withKernel_le hcN (mem_map_of_mem (MulAut.conj c).toMonoidHom h)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    rwa [show c * (c⁻¹ * (k⁻¹ * a * k) * c) * c⁻¹ = k⁻¹ * a * k by group] at this
  refine ⟨c, hc, hES hbE, ?_⟩
  by_cases hiso : ∀ s ∈ S, s * s = 1 → (∀ e ∈ E, s * e = e * s) → s ∈ E
  · have hEC : 2 ≤ Nat.card ↥(E ⊓ coreActionKernel J) := by
      have := Subgroup.card_le_of_le (zpowers_le.mpr (mem_inf.mpr ⟨haE, haK⟩) :
        zpowers a ≤ E ⊓ coreActionKernel J)
      rwa [Nat.card_zpowers, ha2] at this
    obtain ⟨⟨-, hbad, -⟩, -⟩ := GrS5S.l34WCriterionDFact_of_certs G J S hJper hL34
      (GrS4.isSylowTwoIn_inf hS) hS2 hS.1 E hES hE (hE4 hkK) hEC
      fun s hs hss hsc => hiso s (mem_inf.mp hs).1 hss hsc
    rcases hbad with ⟨-, hU⟩ | ⟨hZ16, -⟩
    · exact hU _ hbE hb'K
    · rw [hZ1, Subgroup.card_bot] at hZ16
      norm_num at hZ16
  · push Not at hiso
    obtain ⟨s₀, hs₀S, hs₀2, hs₀E, hs₀n⟩ := hiso
    have hb'E : (k * c)⁻¹ * a * (k * c) ∈ E := hkc ▸ hbE
    obtain ⟨m, hm, hbm⟩ := GrS5S.exists_conj_of_not_isolated hset hcent hWB hSyl hES hE
      (fun e he => hE.1.1 e he _ hb'E) hs₀S hs₀2 hs₀E hs₀n (hs₀E _ hb'E)
    exact absurd ⟨m * c⁻¹, mul_mem hm (hNJ (inv_mem hcN)), by
      calc k⁻¹ * a * k = c * ((k * c)⁻¹ * a * (k * c)) * c⁻¹ := by group
        _ = (m * c⁻¹)⁻¹ * a * (m * c⁻¹) := by rw [hbm]; group⟩ hk

end CFSG.ComponentClassification.GrSLit.KSwOrb

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer

theorem l34Lemma43UnitaryCentreStep_of_max
    (hMax : MaximalTwoComponentInput) : L34Lemma43UnitaryCentreStep := by
  intro G _ _ a x J S A hset hcent hrun h3 hZ1 W hW hWodd hWB hNJ K hKM hKc hKL hsup hSM hSyl
    hSK hKn hOK g hgS hU hno y hyP hyb hy2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hU3, hL34, -, hS, haS, -⟩ := id hset
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hJa : J ≤ centralizer ({a} : Set G) := hU3.2.2.2.1
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hU3.2.2.2.2.1
  have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
  have hP : IsSylowTwoIn (S ⊓ J) J := GrS4.isSylowTwoIn_inf hS
  have hZc : IsCyclic ↥(S ⊓ zStarIn J) := by
    rw [hZ1]
    exact isCyclic_of_subsingleton
  have haK : a ∈ coreActionKernel J := GrS4.mem_coreActionKernel_of_le_centralizer hJa
  have hZJ : zStarIn J = J ⊓ coreActionKernel J := GSThmB.map_fusionZStar_eq J
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS5S.centralizer_le_normalizer_of_sec4 hMax hset
  have hCM : centralizer ({a} : Set G) ≤ normalizer (W : Set G) := hCaN.trans hNJ
  have hSJC : ∀ u ∈ S, u ∈ J → u ∈ coreActionKernel J → u = 1 := by
    intro u huS huJ huC
    have h1 : u ∈ S ⊓ zStarIn J := by
      rw [hZJ]
      exact mem_inf.mpr ⟨huS, mem_inf.mpr ⟨huJ, huC⟩⟩
    rwa [hZ1, mem_bot] at h1
  have hconjJ : ∀ n ∈ normalizer (J : Set G), ∀ u ∈ J, n⁻¹ * u * n ∈ J := by
    intro n hn u hu
    have h1 := (mem_normalizer_iff.mp (inv_mem hn) u).mp hu
    rwa [inv_inv] at h1
  set b : G := g⁻¹ * a * g with hbdef
  have hbK : b ∉ withKernel J := hU.2.2.1
  have hbb : b * b = 1 := hU.2.1
  have hba : b * a = a * b := hcent b hgS
  have hJgb : ∀ u ∈ conjugate J g, u * b = b * u := by
    intro u hu
    have h1 := mem_centralizer_singleton_iff.mp (hJa (mem_conjugate_iff.mp hu))
    calc u * b = g⁻¹ * (g * u * g⁻¹ * a) * g := by rw [hbdef]; group
      _ = g⁻¹ * (a * (g * u * g⁻¹)) * g := by rw [h1]
      _ = b * u := by rw [hbdef]; group
  have hCbJg : ∀ v : G, v * b = b * v → ∀ u ∈ conjugate J g, v⁻¹ * u * v ∈ conjugate J g := by
    intro v hv u hu
    rw [mem_conjugate_iff] at hu ⊢
    have hgv : g * v * g⁻¹ ∈ normalizer (J : Set G) :=
      hCaN (mem_centralizer_singleton_iff.mpr (by
        calc g * v * g⁻¹ * a = g * (v * b) * g⁻¹ := by rw [hbdef]; group
          _ = g * (b * v) * g⁻¹ := by rw [hv]
          _ = a * (g * v * g⁻¹) := by rw [hbdef]; group))
    have h1 := hconjJ _ hgv _ hu
    rwa [show (g * v * g⁻¹)⁻¹ * (g * u * g⁻¹) * (g * v * g⁻¹) = g * (v⁻¹ * u * v) * g⁻¹ by
      group] at h1
  obtain ⟨h, hbh, hSh⟩ := GrS5S.exists_conj_of_le_centralizer hS2 hcent hSyl
    (P := zpowers a) (hS2.to_le (zpowers_le.mpr haS))
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hba.symm))
  have ha'S : h⁻¹ * a * h ∈ S := hSh a (mem_zpowers a)
  have ha'M : ¬ ∃ m ∈ normalizer (W : Set G), h⁻¹ * a * h = m⁻¹ * a * m :=
    fun h' => hno (GrS5S.exists_conj_of_conj hCM hbh h')
  obtain ⟨ha'K, c, hc, ha''S, hU''⟩ :=
    KSwOrb.exists_unitary_conj hset hcent h3 hZ1 hWB hNJ hSyl ha'S ha'M
  have hca : c ∈ centralizer ({a} : Set G) := (mem_inf.mp hc).2
  have hgh : g * h ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr (by
    calc g * h * a = g * (h * (h⁻¹ * b * h)) := by rw [hbh]; group
      _ = a * (g * h) := by rw [hbdef]; group)
  obtain ⟨y', hy'P, hy'b, hy'2, hy'4⟩ :=
    GrS5S.exists_sq_ne_one_of_unitary hJper hL34 hP ha''S hU'' hZc
  set q₀ : G := h * c * y' * (h * c)⁻¹ with hq₀def
  have hq₀a : q₀ * a = a * q₀ := by
    calc q₀ * a = h * c * (y' * (c⁻¹ * (h⁻¹ * a * h) * c)) * (h * c)⁻¹ := by
          rw [hq₀def]; group
      _ = h * c * (c⁻¹ * (h⁻¹ * a * h) * c * y') * (h * c)⁻¹ := by rw [hy'b]
      _ = a * q₀ := by rw [hq₀def]; group
  have hq₀J : q₀ ∈ conjugate J g := by
    rw [mem_conjugate_iff]
    have h1 := hconjJ _ (inv_mem (hCaN (mul_mem hgh hca))) y' (mem_inf.mp hy'P).2
    rwa [show (g * h * c)⁻¹⁻¹ * y' * (g * h * c)⁻¹ = g * q₀ * g⁻¹ by rw [hq₀def]; group] at h1
  have hq₀b : q₀ * b = b * q₀ := hJgb q₀ hq₀J
  have hq₀2 : q₀ * q₀ ≠ 1 := by
    intro h1
    apply hy'2
    calc y' * y' = (h * c)⁻¹ * (q₀ * q₀) * (h * c) := by rw [hq₀def]; group
      _ = 1 := by rw [h1]; group
  have hq₀4 : q₀ * q₀ * (q₀ * q₀) = 1 := by
    calc q₀ * q₀ * (q₀ * q₀) = h * c * (y' * y' * (y' * y')) * (h * c)⁻¹ := by
          rw [hq₀def]; group
      _ = 1 := by rw [hy'4]; group
  have hCSb : S ⊓ centralizer ({b} : Set G) ≤
      centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) := fun s hs =>
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (hcent s (mem_inf.mp hs).1), (mem_inf.mp hs).2⟩
  obtain ⟨T, hT, hST⟩ := GrS4.exists_isSylowTwoIn_le' hCSb (hS2.to_le inf_le_left)
  have hT2 : IsPGroup 2 T := GrS4.isPGroup_of_isSylowTwoIn hT
  have hTa : ∀ t ∈ T, t * a = a * t := fun t ht =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hT.1 ht)).1
  have hTb : ∀ t ∈ T, t * b = b * t := fun t ht =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hT.1 ht)).2
  have hTN : T ≤ normalizer (J : Set G) := fun t ht => hCaN (mem_inf.mp (hT.1 ht)).1
  have hbT : b ∈ T := hST (mem_inf.mpr ⟨hgS, mem_centralizer_singleton_iff.mpr rfl⟩)
  have haT : a ∈ T := hST (mem_inf.mpr ⟨haS, mem_centralizer_singleton_iff.mpr hba.symm⟩)
  have hbN : b ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
    UnbalancedLayer.normalizer_inf_mem (le_normalizer hgS) hU.1
  obtain ⟨-, hcard8, -, hQ8, -, -, -, -⟩ :=
    L34Facts.l34UnitaryCentralizerFact G J (S ⊓ J) b hJper hL34 hU hP hbN
  have hzJ : zStarIn J ≤ J := map_subtype_le _
  obtain ⟨e⟩ := hQ8 (by rw [inf_assoc, inf_eq_right.mpr hzJ, hZ1])
  have hyQ : y ∈ S ⊓ J ⊓ centralizer ({b} : Set G) :=
    mem_inf.mpr ⟨hyP, mem_centralizer_singleton_iff.mpr hyb⟩
  obtain ⟨hy4, hQdich, u, huQ, v, hvQ, huv⟩ := KSwOrb.q8_facts e hyQ hy2
  obtain ⟨S', hS', hTS'⟩ := GrS4.exists_isSylowTwoIn_le' hTN hT2
  have hbN' : b ∈ normalizer ((S' ⊓ J : Subgroup G) : Set G) :=
    UnbalancedLayer.normalizer_inf_mem (le_normalizer (hTS' hbT)) hU.1
  obtain ⟨-, hcard8', -⟩ := L34Facts.l34UnitaryCentralizerFact G J (S' ⊓ J) b hJper hL34 hU
    (GrS4.isSylowTwoIn_inf hS') hbN'
  have hQT : ∀ w ∈ S ⊓ J ⊓ centralizer ({b} : Set G), w ∈ T := fun w hw =>
    hST (mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hw).1).1, (mem_inf.mp hw).2⟩)
  have hTJ : T ⊓ J = S ⊓ J ⊓ centralizer ({b} : Set G) := by
    have hle : S ⊓ J ⊓ centralizer ({b} : Set G) ≤ T ⊓ J := fun w hw =>
      mem_inf.mpr ⟨hQT w hw, (mem_inf.mp (mem_inf.mp hw).1).2⟩
    have hle' : T ⊓ J ≤ S' ⊓ J ⊓ centralizer ({b} : Set G) := fun w hw =>
      mem_inf.mpr ⟨mem_inf.mpr ⟨hTS' (mem_inf.mp hw).1, (mem_inf.mp hw).2⟩,
        (mem_inf.mp (hT.1 (mem_inf.mp hw).1)).2⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcard8]
    exact hcard8' ▸ Subgroup.card_le_of_le hle'
  set z : G := y * y with hzdef
  have hzQ : z ∈ S ⊓ J ⊓ centralizer ({b} : Set G) := mul_mem hyQ hyQ
  have hzS : z ∈ S := (mem_inf.mp (mem_inf.mp hzQ).1).1
  have hzJ' : z ∈ J := (mem_inf.mp (mem_inf.mp hzQ).1).2
  have hzb : z * b = b * z := mem_centralizer_singleton_iff.mp (mem_inf.mp hzQ).2
  have hza : z * a = a * z := mem_centralizer_singleton_iff.mp (hJa hzJ')
  have hzT : z ∈ T := hQT z hzQ
  have hzz : z * z = 1 := hy4
  have hz1 : z ≠ 1 := hy2
  have hzc : ∀ t ∈ T, z * t = t * z := by
    intro t ht
    have hmem : t⁻¹ * z * t ∈ S ⊓ J ⊓ centralizer ({b} : Set G) := by
      rw [← hTJ]
      exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem ht) hzT) ht, hconjJ t (hTN ht) z hzJ'⟩
    have hne : t⁻¹ * z * t ≠ 1 := fun h1 => hz1 (by
      calc z = t * (t⁻¹ * z * t) * t⁻¹ := by group
        _ = 1 := by rw [h1]; group)
    rcases hQdich _ hmem hne with h1 | h1
    · calc z * t = t * (t⁻¹ * z * t) := by group
        _ = t * z := by rw [h1]
    · exfalso
      apply hz1
      rw [show t⁻¹ * z * t * (t⁻¹ * z * t) = t⁻¹ * (z * z) * t by group, hzz,
        show t⁻¹ * 1 * t = 1 by group] at h1
      exact h1.symm
  have hq₀H : q₀ ∈ centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G) :=
    mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hq₀a, mem_centralizer_singleton_iff.mpr hq₀b⟩
  obtain ⟨η, hηH, hηq⟩ := GrS5.exists_conj_mem_of_isSylowTwoIn hT hq₀H
    (KSwOrb.isPGroup_zpowers_of_four hq₀4)
  set q : G := η⁻¹ * q₀ * η with hqdef
  have hqT : q ∈ T := hηq
  have hqJg : q ∈ conjugate J g :=
    hCbJg η (mem_centralizer_singleton_iff.mp (mem_inf.mp hηH).2) q₀ hq₀J
  have hq2 : q * q ≠ 1 := by
    intro h1
    apply hq₀2
    calc q₀ * q₀ = η * (q * q) * η⁻¹ := by rw [hqdef]; group
      _ = 1 := by rw [h1]; group
  have hq4 : q * q * (q * q) = 1 := by
    calc q * q * (q * q) = η⁻¹ * (q₀ * q₀ * (q₀ * q₀)) * η := by rw [hqdef]; group
      _ = 1 := by rw [hq₀4]; group
  by_contra hz
  have hcomm : ∀ w ∈ S ⊓ J ⊓ centralizer ({b} : Set G), w * q = q * w := by
    intro w hw
    have hwT : w ∈ T := hQT w hw
    have hwJ : w ∈ J := (mem_inf.mp (mem_inf.mp hw).1).2
    have hwb : w * b = b * w := mem_centralizer_singleton_iff.mp (mem_inf.mp hw).2
    have hcT : w⁻¹ * q⁻¹ * w * q ∈ T :=
      mul_mem (mul_mem (mul_mem (inv_mem hwT) (inv_mem hqT)) hwT) hqT
    have hcJ : w⁻¹ * q⁻¹ * w * q ∈ J := by
      rw [show w⁻¹ * q⁻¹ * w * q = w⁻¹ * (q⁻¹ * w * q) by group]
      exact mul_mem (inv_mem hwJ) (hconjJ q (hTN hqT) w hwJ)
    have hcJg : w⁻¹ * q⁻¹ * w * q ∈ conjugate J g :=
      mul_mem (hCbJg w hwb _ (inv_mem hqJg)) hqJg
    by_cases h1 : w⁻¹ * q⁻¹ * w * q = 1
    · calc w * q = q * w * (w⁻¹ * q⁻¹ * w * q) := by group
        _ = q * w := by rw [h1, mul_one]
    · exfalso
      have hmem : w⁻¹ * q⁻¹ * w * q ∈ S ⊓ J ⊓ centralizer ({b} : Set G) := by
        rw [← hTJ]
        exact mem_inf.mpr ⟨hcT, hcJ⟩
      rcases hQdich _ hmem h1 with h2 | h2
      · exact hz (h2 ▸ hcJg)
      · exact hz (h2 ▸ mul_mem hcJg hcJg)
  have hca' : ∀ e ∈ zpowers a, ∀ t : G, t * a = a * t → e * t = t * e := fun e he t ht => by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp he
    exact Commute.zpow_left ht.symm n
  have hcb : ∀ e ∈ zpowers a, e * b = b * e := fun e he => hca' e he b hba
  have hbE₁ : b ∉ zpowers a := fun h1 =>
    (GrS4.eq_one_or_eq_of_mem_zpowers haa h1).elim (fun h2 => hbK (h2 ▸ one_mem _))
      (fun h2 => hbK (h2 ▸ mem_sup_right haK))
  obtain ⟨hE₂, hE₂c⟩ := GrS4.isElemTwo_sup_zpowers (isElemTwo_zpowers haa) hbb hbE₁ hcb
  have hzE₂ : z ∉ zpowers a ⊔ zpowers b := by
    intro h1
    rcases GrS4.mem_or_mul_of_mem_sup_zpowers hbb hcb h1 with h2 | ⟨e', he', h2⟩
    · rcases GrS4.eq_one_or_eq_of_mem_zpowers haa h2 with h3 | h3
      · exact hz1 h3
      · exact ha1 (hSJC a haS (h3 ▸ hzJ') haK)
    · apply hbK
      rw [show b = e'⁻¹ * z by rw [h2]; group]
      exact mul_mem (inv_mem (mem_sup_right (zpowers_le.mpr haK he'))) (mem_sup_left hzJ')
  have hcz : ∀ e ∈ zpowers a ⊔ zpowers b, e * z = z * e := by
    have hle : zpowers a ⊔ zpowers b ≤ centralizer ({z} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hza.symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzb.symm))
    exact fun e he => mem_centralizer_singleton_iff.mp (hle he)
  obtain ⟨hE₃, hE₃c⟩ := GrS4.isElemTwo_sup_zpowers hE₂ hzz hzE₂ hcz
  have hE : IsEightGroup (zpowers a ⊔ zpowers b ⊔ zpowers z) :=
    ⟨hE₃, by rw [hE₃c, hE₂c, Nat.card_zpowers, ha2]⟩
  have hET : zpowers a ⊔ zpowers b ⊔ zpowers z ≤ T :=
    sup_le (sup_le (zpowers_le.mpr haT) (zpowers_le.mpr hbT)) (zpowers_le.mpr hzT)
  set s : G := q * q with hsdef
  have hsT : s ∈ T := mul_mem hqT hqT
  have hsE : s ∈ zpowers a ⊔ zpowers b ⊔ zpowers z := by
    by_contra hsn
    have hle : zpowers a ⊔ zpowers b ⊔ zpowers z ≤ centralizer ({s} : Set G) := sup_le (sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hTa s hsT).symm))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hTb s hsT).symm)))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hzc s hsT)))
    exact hno (KSwOrb.exists_conj_of_two_rank hset hcent hWB hSyl hCM
      (hET.trans fun t ht => (mem_inf.mp (hT.1 ht)).1) hE (fun e he => hTb e (hET he))
      (hTa s hsT) hq4 (fun e he => (mem_centralizer_singleton_iff.mp (hle he)).symm) hsn
      (hTb s hsT))
  have hsJg : s ∈ conjugate J g := mul_mem hqJg hqJg
  have hsa1 : s ≠ a := by
    intro h1
    have h2 : g * a * g⁻¹ ∈ J := mem_conjugate_iff.mp (h1 ▸ hsJg)
    have h3 := hconjJ _ (hCaN hgh) _ h2
    rw [show (g * h)⁻¹ * (g * a * g⁻¹) * (g * h) = h⁻¹ * a * h by group] at h3
    exact ha'K (mem_sup_left h3)
  have hsC : s ∉ coreActionKernel J := by
    intro hsK
    rcases GrS4.mem_or_mul_of_mem_sup_zpowers hzz hcz hsE with h1 | ⟨e, he, h1⟩
    · rcases GrS4.mem_or_mul_of_mem_sup_zpowers hbb hcb h1 with h2 | ⟨e', he', h2⟩
      · rcases GrS4.eq_one_or_eq_of_mem_zpowers haa h2 with h3 | h3
        · exact hq2 h3
        · exact hsa1 h3
      · apply hbK
        rw [show b = e'⁻¹ * s by rw [h2]; group]
        exact mem_sup_right (mul_mem (inv_mem (zpowers_le.mpr haK he')) hsK)
    · rcases GrS4.mem_or_mul_of_mem_sup_zpowers hbb hcb he with h2 | ⟨e', he', h2⟩
      · apply hz1
        refine hSJC z hzS hzJ' ?_
        rw [show z = e⁻¹ * s by rw [h1]; group]
        rcases GrS4.eq_one_or_eq_of_mem_zpowers haa h2 with h3 | h3
        · rw [h3, inv_one, one_mul]
          exact hsK
        · rw [h3]
          exact mul_mem (inv_mem haK) hsK
      · apply hbK
        rw [show b = e'⁻¹ * s * z⁻¹ by rw [h1, h2]; group]
        exact mul_mem (mul_mem (inv_mem (mem_sup_right (zpowers_le.mpr haK he')))
          (mem_sup_right hsK)) (inv_mem (mem_sup_left hzJ'))
  obtain ⟨-, -, h3c⟩ := HSFLit.AutL34.l34UnitaryAutFact G J T b hJper hL34 hU hT2
    (fun t ht => mem_inf.mpr ⟨hTN ht, mem_centralizer_singleton_iff.mpr (hTb t ht)⟩)
  have huvK := h3c q hqT hsC u (hQT u huQ) v (hQT v hvQ) (hcomm u huQ) (hcomm v hvQ)
  have huS : u ∈ S := (mem_inf.mp (mem_inf.mp huQ).1).1
  have hvS : v ∈ S := (mem_inf.mp (mem_inf.mp hvQ).1).1
  have huJ : u ∈ J := (mem_inf.mp (mem_inf.mp huQ).1).2
  have hvJ : v ∈ J := (mem_inf.mp (mem_inf.mp hvQ).1).2
  have h1 : u⁻¹ * v⁻¹ * u * v = 1 := hSJC _
    (mul_mem (mul_mem (mul_mem (inv_mem huS) (inv_mem hvS)) huS) hvS)
    (mul_mem (mul_mem (mul_mem (inv_mem huJ) (inv_mem hvJ)) huJ) hvJ) huvK
  apply huv
  calc u * v = v * u * (u⁻¹ * v⁻¹ * u * v) := by group
    _ = v * u := by rw [h1, mul_one]

theorem l34Lemma43UnitaryStep_of_max
    (hMax : MaximalTwoComponentInput) : L34Lemma43UnitaryStep :=
  l34Lemma43UnitaryStep_of_centre hMax (l34Lemma43UnitaryCentreStep_of_max hMax)

end CFSG.ComponentClassification.GrSLit
