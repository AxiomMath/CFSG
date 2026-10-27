module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAut
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentCited
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentFrattiniTriv
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepFiveFour
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentPQ
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentStepZero
import Certificates.Kernel.Sporadic.Fi22.C2068
import Certificates.Kernel.Sporadic.Fi22.C3151

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent

open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_pow_two_pow_eq_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {k e : ℕ}
    (h2 : x ^ (2 ^ k) = 1) (hpe : x ^ (p ^ e) = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (p ^ e) :=
    Nat.Coprime.pow k e ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  have h := mem_of_pow_mem_of_coprime' (H := ⊥) hcop (by rw [h2]; exact Subgroup.one_mem _)
    (by rw [hpe]; exact Subgroup.one_mem _)
  exact Subgroup.mem_bot.mp h

theorem commute_of_commutator_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {B B₁ L : Subgroup G}
    (hB : IsPGroup p B) (hB₁B : B₁ ≤ B) (hB₁L : B₁ ≤ L) {c : G} (hcB : c ∈ B)
    (hcL : ⁅Subgroup.zpowers c, L⁆ ≤ pCoreOf 2 L) : ∀ u ∈ B₁, c * u = u * c := by
  intro u hu
  have hm : c * u * c⁻¹ * u⁻¹ ∈ pCoreOf 2 L := by
    have := hcL (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers c) (hB₁L hu))
    simpa [commutatorElement_def] using this
  have hmB : c * u * c⁻¹ * u⁻¹ ∈ B :=
    B.mul_mem (B.mul_mem (B.mul_mem hcB (hB₁B hu)) (B.inv_mem hcB)) (B.inv_mem (hB₁B hu))
  obtain ⟨e, he⟩ := hB ⟨_, hmB⟩
  have h2 : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.pCore_isPGroup.map _
  obtain ⟨k, hk⟩ := h2 ⟨_, hm⟩
  have h1 := eq_one_of_pow_two_pow_eq_one (Fact.out : p.Prime) hp2
    (by simpa using congrArg Subtype.val hk) (by simpa using congrArg Subtype.val he)
  calc c * u = (c * u * c⁻¹ * u⁻¹) * (u * c) := by group
    _ = u * c := by rw [h1, one_mul]

theorem pow_eq_one_of_conj_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {H : Subgroup G}
    {b b₁ t n : G} {i m : ℕ} (hb₁ : b₁ ∈ H) (htH : t * b₁ * t⁻¹ ∈ H) (hbH : b ∉ H)
    (hbo : orderOf b = p) (hbt : Commute b t) (hbb₁ : Commute b b₁) (hm : Nat.Coprime m p)
    (hn : n ^ m = 1) (he : t * (b₁ * b ^ i) * t⁻¹ = (b₁ * b ^ i)⁻¹ * n) : b ^ i = 1 := by
  have hp : p.Prime := Fact.out
  set k := b₁ * (t * b₁ * t⁻¹) with hk
  have hkH : k ∈ H := H.mul_mem hb₁ htH
  have hbc : Commute b (t * b₁ * t⁻¹) := (hbt.mul_right hbb₁).mul_right hbt.inv_right
  have hbk : Commute b k := hbb₁.mul_right hbc
  have hn' : n = k * b ^ (2 * i) := by
    have h1 : n = (b₁ * b ^ i) * (t * (b₁ * b ^ i) * t⁻¹) := by rw [he]; group
    have h2 : t * b ^ i * t⁻¹ = b ^ i := by
      rw [← (hbt.pow_left i).eq]
      group
    calc n = b₁ * b ^ i * (t * b₁ * t⁻¹) * (t * b ^ i * t⁻¹) := by rw [h1]; group
      _ = b₁ * (b ^ i * (t * b₁ * t⁻¹)) * b ^ i := by rw [h2]; group
      _ = k * b ^ (2 * i) := by rw [(hbc.pow_left i).eq, hk, two_mul, pow_add]; group
  have hzm : (b ^ (2 * i)) ^ m ∈ H := by
    have h := hn
    rw [hn', ((hbk.pow_left (2 * i)).symm).mul_pow] at h
    rw [eq_inv_of_mul_eq_one_right h]
    exact H.inv_mem (H.pow_mem hkH m)
  have hzp : (b ^ (2 * i)) ^ p ∈ H := by
    rw [← pow_mul, mul_comm, pow_mul, ← hbo, pow_orderOf_eq_one, one_pow]
    exact H.one_mem
  have hz : b ^ (2 * i) ∈ H := mem_of_pow_mem_of_coprime' hm hzm hzp
  have hdvd : p ∣ 2 * i := by
    by_contra hnd
    have hcop : Nat.Coprime (2 * i) p := (Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hnd))
    refine hbH (mem_of_pow_mem_of_coprime' hcop hz ?_)
    rw [← hbo, pow_orderOf_eq_one]
    exact H.one_mem
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h2 | hi
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hp2
  · exact orderOf_dvd_iff_pow_eq_one.mp (hbo ▸ hi)

section Generic

variable {p : ℕ} [Fact p.Prime] {C : Subgroup G}
  {K : Subgroup (C ⧸ primeComplementCore (G := C) p)} [hK : K.Normal]

local notation "φ" => RankOneSylow.act (primeComplementCore (G := C) p) K

theorem mem_hyp111Pre_of_conj_eq (hI5 : KFactStepThreeCentSylow) (hp2 : p ≠ 2)
    (hZ : Subgroup.center ↥K = ⊥) (hSt : StepThreeGroup p ↥K)
    (hXr : Open.pRank p (d1PlusCore p C K) ≤ 1) {B : Subgroup G}
    (hBC : CFSG.ABGLocalTools.IsSylowOf p B C) {b : G} (hbC : b ∈ C)
    (hb : ∀ c ∈ C, b * c = c * b) (hbo : orderOf b = p) {c : G} (hcB : c ∈ B) (hcp : c ^ p = 1)
    (hcB₁ : ∀ u ∈ B ⊓ hyp111Pre p C K, c * u = u * c) {t n : G} {m : ℕ} (htC : t ∈ C)
    (hm : Nat.Coprime m p) (hn : n ^ m = 1) (he : t * c * t⁻¹ = c⁻¹ * n) :
    c ∈ hyp111Pre p C K := by
  have hp : p.Prime := Fact.out
  have hB : IsPGroup p B := by
    obtain ⟨Q, rfl⟩ := hBC
    exact Q.isPGroup'.map _
  have hcC : c ∈ C := hBC.le hcB
  have hbX : b ∈ d1PlusCore p C K := mem_d1PlusCore_of_central hbC hb K
  have hbK : b ∉ hyp111Pre p C K := not_mem_hyp111Pre hZ hbX hbo
  set S : Subgroup (MulAut ↥K) := ((B ⊓ hyp111Pre p C K).subgroupOf C).map φ with hS
  have hcent : φ ⟨c, hcC⟩ ∈ Subgroup.centralizer (S : Set (MulAut ↥K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcB₁ u (Subgroup.mem_subgroupOf.mp hu)).symm
  have hcS := hI5 p (MulAut ↥K) _ S conj_range_normal (centralizer_conj_range_eq_bot hZ)
    (stepThreeGroup_conj_range hZ hSt) (isSylowOf_act hZ hBC) _ hcent 1
    (by rw [pow_one, ← map_pow, show (⟨c, hcC⟩ : C) ^ p = 1 from Subtype.ext (by simpa using hcp),
      map_one])
  obtain ⟨u, hu, hue⟩ := hcS
  have hu' := Subgroup.mem_subgroupOf.mp hu
  set x : G := (u : G)⁻¹ * c with hx
  have hxX : x ∈ d1PlusCore p C K := by
    have h : u⁻¹ * ⟨c, hcC⟩ ∈ MonoidHom.ker φ := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hue, inv_mul_cancel]
    exact (mem_d1PlusCore_iff_mem_ker _).mpr h
  have hxB : x ∈ B := B.mul_mem (B.inv_mem hu'.1) hcB
  have hux : (u : G) * x = x * u := commute_of_mem_inf hK hZ hBC.le hB hu'.1 hxB hu'.2 hxX
  have hcux : c = u * x := by rw [hx]; group
  have hxp : x ^ p = 1 := by
    have h1 : (u : G) ^ p * x ^ p = 1 := by
      rw [← (Commute.mul_pow hux), ← hcux, hcp]
    have hxpK : x ^ p ∈ hyp111Pre p C K := by
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hu'.2 p)
    obtain ⟨e, he'⟩ := hB ⟨_, B.pow_mem hxB p⟩
    exact eq_one_of_mem_inf hZ hxpK (Subgroup.pow_mem _ hxX p)
      (n := e) (by simpa using congrArg Subtype.val he')
  have hxb : x ∈ Subgroup.zpowers b := by
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    · have hXC : d1PlusCore p C K ≤ C := Subgroup.map_subtype_le _
      exact mem_zpowers_of_pRank_le_one hp hXr hbX hbo (fun y hy => hb y (hXC hy)) hxX
        (orderOf_eq_prime hxp hx1)
  obtain ⟨i, hi⟩ := (mem_powers_iff_mem_zpowers).mpr hxb
  have hcui : c = u * b ^ i := by rw [hcux, ← hi]
  have hbi := pow_eq_one_of_conj_eq hp2 hu'.2 (conj_mem_hyp111Pre htC hu'.2) hbK hbo
    (hb t htC) (hb u (hBC.le hu'.1)) hm hn (hcui ▸ he)
  rw [hcui, hbi, mul_one]
  exact hu'.2

end Generic

section Field

variable {p : ℕ} [Fact p.Prime] {H : Subgroup G}
  {KH : Subgroup (H ⧸ primeComplementCore (G := H) p)} [hKH : KH.Normal]

local notation "ψ" => RankOneSylow.act (primeComplementCore (G := H) p) KH

theorem caseTwo_conj_range {K : Type} [Group K] (hZ : Subgroup.center K = ⊥)
    (h : IsCaseTwoGroup p K) :
    (p = 3 ∧ ∃ (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower), q.p = 2 ∧
        q.exponent = 3 ∧ d.1 = .A 1 q ∧
        Nonempty (↥(MulAut.conj : K →* MulAut K).range ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      (p = 5 ∧ ∃ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 ∧
        Nonempty (↥(MulAut.conj : K →* MulAut K).range ≃* (TauCeti.CFSGIndex.lie d).Group)) := by
  obtain ⟨d, hd, ⟨e⟩⟩ := h
  have e' := (MonoidHom.ofInjective (conj_injective_of_center hZ)).symm.trans e
  rcases hd with ⟨h3, q, hq2, hq3, hdq⟩ | ⟨h5, hd5⟩
  · exact Or.inl ⟨h3, d, q, hq2, hq3, hdq, ⟨e'⟩⟩
  · exact Or.inr ⟨h5, d, hd5, ⟨e'⟩⟩

theorem exists_inv_mod_core (hFld : KFactFieldAutInvert) (hKc : IsCaseTwoGroup p ↥KH)
    (hZ : Subgroup.center ↥KH = ⊥) {b c : G} (hbH : b ∈ H) (hbo : orderOf b = p)
    (hbK : b ∉ hyp111Pre p H KH ⊔ d1PlusCore p H KH) (hcK : c ∈ hyp111Pre p H KH)
    (hco : orderOf c = p) (hbc : b * c = c * b) :
    ∃ t ∈ H, b * t = t * b ∧
      c * (t * c * t⁻¹) ∈ (primeComplementCore (G := H) p).map H.subtype := by
  have hp : p.Prime := Fact.out
  set O := primeComplementCore (G := H) p with hO
  obtain ⟨c', hc'K, rfl⟩ := hcK
  set bb : H := ⟨b, hbH⟩ with hbb
  have hKp : ∀ h : H, (h : H ⧸ O) ∈ KH → (h : G) ∈ hyp111Pre p H KH := fun h hh => ⟨h, hh, rfl⟩
  have hψp : ψ bb ^ p = 1 := by
    rw [← map_pow, show bb ^ p = 1 from Subtype.ext (by simp [hbb, ← hbo, pow_orderOf_eq_one]),
      map_one]
  have hψ1 : ψ bb ≠ 1 := fun h1 =>
    hbK (Subgroup.mem_sup_right ((mem_d1PlusCore_iff_mem_ker bb).mpr (MonoidHom.mem_ker.mpr h1)))
  have hψo : orderOf (ψ bb) = p := orderOf_eq_prime hψp hψ1
  have hψI : ψ bb ∉ (MulAut.conj : ↥KH →* MulAut ↥KH).range := by
    rintro ⟨k, hk⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective O (k : H ⧸ O)
    have hhK : (h : H ⧸ O) ∈ KH := by rw [← QuotientGroup.mk'_apply, hh]; exact k.2
    have hact : ψ h = MulAut.conj k := by
      rw [RankOneSylow.act_eq_conj hhK]
      congr 1
      exact Subtype.ext hh
    have hX : ((h⁻¹ * bb : H) : G) ∈ d1PlusCore p H KH := by
      refine (mem_d1PlusCore_iff_mem_ker _).mpr (MonoidHom.mem_ker.mpr ?_)
      rw [map_mul, map_inv, hact, hk, inv_mul_cancel]
    apply hbK
    have e : b = (h : G) * ((h⁻¹ * bb : H) : G) := by simp [hbb]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hKp h hhK)) (Subgroup.mem_sup_right hX)
  have hcI : ψ c' ∈ (MulAut.conj : ↥KH →* MulAut ↥KH).range := by
    rw [RankOneSylow.act_eq_conj hc'K]
    exact ⟨_, rfl⟩
  have hc'o : orderOf c' = p := by rw [← Subgroup.orderOf_coe]; exact hco
  have hc'p : c' ^ p = 1 := hc'o ▸ pow_orderOf_eq_one c'
  have hψc : orderOf (ψ c') = p := by
    refine orderOf_eq_prime (by rw [← map_pow, hc'p, map_one]) fun h1 => ?_
    rw [RankOneSylow.act_eq_conj hc'K, ← (MulAut.conj : ↥KH →* MulAut ↥KH).map_one] at h1
    have h2 := congrArg Subtype.val (conj_injective_of_center hZ h1)
    have hcore : c' ∈ O := (QuotientGroup.eq_one_iff c').mp h2
    have hc1 := eq_one_of_mem_core hcore (n := 1) (by rw [pow_one]; exact hc'p)
    rw [hc1, orderOf_one] at hc'o
    exact hp.one_lt.ne hc'o
  have hbc' : bb * c' = c' * bb := Subtype.ext hbc
  have hcφ : ψ c' ∈ Subgroup.centralizer ({ψ bb} : Set (MulAut ↥KH)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hbc']
  obtain ⟨τ, ⟨⟨k, rfl⟩, hτφ⟩, -, hτc⟩ := hFld p (MulAut ↥KH) _ conj_range_normal
    (centralizer_conj_range_eq_bot hZ) (caseTwo_conj_range hZ hKc) (ψ bb) hψo hψI (ψ c')
    ⟨hcI, hcφ⟩ hψc
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective O (k : H ⧸ O)
  have hhK : (h : H ⧸ O) ∈ KH := by rw [← QuotientGroup.mk'_apply, hh]; exact k.2
  have hact : ψ h = MulAut.conj k := by
    rw [RankOneSylow.act_eq_conj hhK]
    congr 1
    exact Subtype.ext hh
  have hcomm : bb * h * bb⁻¹ * h⁻¹ ∈ O := by
    have hτφ' := Subgroup.mem_centralizer_singleton_iff.mp hτφ
    refine mem_core_of_mem_inf hZ ?_ ?_
    · have h1 := conj_mem_hyp111Pre (K := KH) hbH (hKp h hhK)
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hKp h hhK))
      simpa using this
    · refine (mem_d1PlusCore_iff_mem_ker _).mpr (MonoidHom.mem_ker.mpr ?_)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hact, ← hτφ']
      group
  have hinv : c' * (h * c' * h⁻¹) ∈ O := by
    refine mem_core_of_mem_inf hZ ?_ ?_
    · have h1 := conj_mem_hyp111Pre (K := KH) (Subgroup.map_subtype_le _ (hKp h hhK))
        (hKp c' hc'K)
      have := Subgroup.mul_mem _ (hKp c' hc'K) h1
      simpa using this
    · refine (mem_d1PlusCore_iff_mem_ker _).mpr (MonoidHom.mem_ker.mpr ?_)
      rw [map_mul, map_mul, map_mul, map_inv, hact, hτc, mul_inv_cancel]
  have hnorm : ∀ g : H, g ∈ Subgroup.normalizer (O : Set H) := fun g =>
    Subgroup.mem_normalizer_iff.mpr fun n =>
      ⟨fun hn => (inferInstance : O.Normal).conj_mem n hn g, fun hn => by
        simpa [mul_assoc] using (inferInstance : O.Normal).conj_mem _ hn g⁻¹⟩
  have hbp : IsPGroup p (Subgroup.zpowers bb) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe]
    exact hbo
  obtain ⟨n, hn, hcn⟩ := exists_commute_mul_of_comm_mem hbp (primeComplementCore_coprime p).symm
    (hnorm bb) (hnorm h) hcomm
  refine ⟨((h * n : H) : G), (h * n).2, ?_, ?_⟩
  · exact (congrArg Subtype.val hcn.eq).symm
  · refine ⟨c' * ((h * n) * c' * (h * n)⁻¹), (QuotientGroup.eq_one_iff _).mp ?_, by simp⟩
    rw [← QuotientGroup.eq_one_iff] at hinv
    have hn1 : ((n : H) : H ⧸ O) = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_rev] at hinv ⊢
    rw [hn1]
    simpa [mul_assoc] using hinv

end Field

end CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent
