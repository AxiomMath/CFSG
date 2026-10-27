module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.S10.StrongCover
public import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

section Frattini

variable {H M : Type} [Group H] [Finite H] [Group M]

private theorem fusionIsSylowIn_two_of_card {S P : Subgroup H} (hSP : S ≤ P)
    (hS : IsPGroup 2 S) {m : ℕ} (hm : ¬ 2 ∣ m) (hcard : Nat.card P = Nat.card S * m) :
    fusionIsSylowIn 2 S P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hSP, hS, fun Q hQP hQ hSQ => ?_⟩
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  obtain ⟨b, hb⟩ := hS.exists_card_eq
  have hdvd : Nat.card Q ∣ Nat.card P := Subgroup.card_dvd_of_le hQP
  rw [hcard, ha, hb] at hdvd
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
  have h1 : 2 ^ a ∣ 2 ^ b := hcop.dvd_of_dvd_mul_right hdvd
  have h2 : Nat.card Q ≤ Nat.card S := by
    rw [ha, hb]
    exact Nat.le_of_dvd (by positivity) h1
  exact (Subgroup.eq_of_le_of_card_ge hSQ h2).symm

private theorem mem_normalizer_of_map_conj_eq {S : Subgroup H} {g : H}
    (h : S.map (MulAut.conj g).toMonoidHom = S) : g ∈ Subgroup.normalizer (S : Set H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : g * y * g⁻¹ ∈ S.map (MulAut.conj g).toMonoidHom := ⟨y, hy, rfl⟩
    rwa [h] at this
  · intro hy
    rw [← h] at hy
    obtain ⟨s, hs, hsy⟩ := hy
    have hsy' : g * s * g⁻¹ = g * y * g⁻¹ := hsy
    have : s = y := by simpa using hsy'
    exact this ▸ hs

private theorem map_conj_map_conj (S : Subgroup H) (a b : H) :
    (S.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      S.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem exists_mem_normalizer_centralizer_map_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (π : H →* M) (hkp : ¬ p ∣ Nat.card π.ker) (hk2 : ¬ 2 ∣ Nat.card π.ker)
    {S D : Subgroup H} (hS : IsPGroup 2 S) (hSinj : Function.Injective (π.comp S.subtype))
    (hD : IsPGroup p D) (hDS : D ≤ Subgroup.normalizer (S : Set H)) {h : H}
    (hhD : ∀ d ∈ D, d * h = h * d)
    (hh : π h ∈ Subgroup.normalizer ((S.map π : Subgroup M) : Set M)) :
    ∃ g ∈ Subgroup.normalizer (S : Set H) ⊓ Subgroup.centralizer (D : Set H), π g = π h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup H := (S.map π).comap π with hPdef
  set S' : Subgroup H := S.map (MulAut.conj h).toMonoidHom with hS'def
  have hSP : S ≤ P := Subgroup.le_comap_map π S
  have hSk : S ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxk⟩
    have : (⟨x, hxS⟩ : S) = 1 := hSinj (by simpa using hxk)
    exact congrArg Subtype.val this
  have hPcard : Nat.card P = Nat.card S * Nat.card π.ker := by
    have hP : P = π.ker ⊔ S := by rw [hPdef, Subgroup.comap_map_eq, sup_comm]
    have h1 := card_sup_mul_card_inf_of_normal π.ker S
    rw [inf_comm, hSk, Subgroup.card_bot, mul_one, ← hP] at h1
    rw [h1, mul_comm]
  have hS'P : S' ≤ P := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hPdef, Subgroup.mem_comap]
    have e : π ((MulAut.conj h).toMonoidHom s) = π h * π s * (π h)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 hh (π s)).1 (Subgroup.mem_map_of_mem π hs)
  have hS'card : Nat.card S' = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hSyl : fusionIsSylowIn 2 S P := fusionIsSylowIn_two_of_card hSP hS hk2 hPcard
  have hSyl' : fusionIsSylowIn 2 S' P :=
    fusionIsSylowIn_two_of_card hS'P (hS.map _) hk2 (by rw [hPcard, hS'card])
  have hPp : ¬ p ∣ Nat.card P := by
    rw [hPcard]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
    · obtain ⟨b, hb⟩ := hS.exists_card_eq
      rw [hb] at h1
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1))
    · exact hkp h1
  have hDP : D ≤ Subgroup.normalizer (P : Set H) := by
    intro d hd
    have hdN : π d ∈ Subgroup.normalizer ((S.map π : Subgroup M) : Set M) :=
      Subgroup.le_normalizer_map π ⟨d, hDS hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hPdef, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 hdN (π y)
  have hDS' : D ≤ Subgroup.normalizer (S' : Set H) := by
    have key : ∀ d ∈ D, ∀ t ∈ S', d * t * d⁻¹ ∈ S' := by
      rintro d hd _ ⟨s, hs, rfl⟩
      have hdh : d * h = h * d := hhD d hd
      refine ⟨d * s * d⁻¹, (Subgroup.mem_normalizer_iff.1 (hDS hd) s).1 hs, ?_⟩
      simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc h * (d * s * d⁻¹) * h⁻¹ = (h * d) * s * (h * d)⁻¹ := by group
        _ = (d * h) * s * (d * h)⁻¹ := by rw [hdh]
        _ = d * (h * s * h⁻¹) * d⁻¹ := by group
    intro d hd
    exact S10.mem_normalizer_of_conj' (key d hd) (fun t ht => by
      simpa using key d⁻¹ (D.inv_mem hd) t ht)
  obtain ⟨c, ⟨hcP, hcD⟩, hc⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows hp
    Nat.prime_two hD hPp hDP hSyl hSyl' hDS hDS'
  obtain ⟨s, hsS, hsc⟩ : π c ∈ S.map π := hcP
  have hcD' : ∀ d ∈ D, d * c = c * d := fun d hd => Subgroup.mem_centralizer_iff.1 hcD d hd
  have hsD : s ∈ Subgroup.centralizer (D : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hds : d * s * d⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hDS hd) s).1 hsS
    have h1 : π (d * s * d⁻¹) = π s := by
      rw [map_mul, map_mul, map_inv, hsc, ← map_inv, ← map_mul, ← map_mul, hcD' d hd,
        mul_inv_cancel_right]
    have h2 : (⟨d * s * d⁻¹, hds⟩ : S) = ⟨s, hsS⟩ := hSinj (by simpa using h1)
    have h3 : d * s * d⁻¹ = s := congrArg Subtype.val h2
    calc d * s = d * s * d⁻¹ * d := by group
      _ = s * d := by rw [h3]
  have hhD' : h ∈ Subgroup.centralizer (D : Set H) :=
    Subgroup.mem_centralizer_iff.2 fun d hd => hhD d hd
  refine ⟨s * (c⁻¹ * h), ⟨?_, ?_⟩, ?_⟩
  ·
    have hch : S.map (MulAut.conj (c⁻¹ * h)).toMonoidHom = S := by
      rw [← map_conj_map_conj, ← hS'def, hc, map_conj_map_conj, inv_mul_cancel]
      ext y
      simp
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hsS) (mem_normalizer_of_map_conj_eq hch)
  · exact Subgroup.mul_mem _ hsD (Subgroup.mul_mem _ (Subgroup.inv_mem _ hcD) hhD')
  · rw [map_mul, map_mul, map_inv, hsc, mul_inv_cancel_left]

theorem map_normalizer_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (π : H →* M)
    (hπ : Function.Surjective π) (hkp : ¬ p ∣ Nat.card π.ker) (hk2 : ¬ 2 ∣ Nat.card π.ker)
    {S : Subgroup H} (hS : IsPGroup 2 S) (hSinj : Function.Injective (π.comp S.subtype)) :
    (Subgroup.normalizer (S : Set H)).map π =
      Subgroup.normalizer ((S.map π : Subgroup M) : Set M) := by
  refine le_antisymm (Subgroup.le_normalizer_map π) fun m hm => ?_
  obtain ⟨h, rfl⟩ := hπ m
  obtain ⟨g, hg, hgh⟩ := exists_mem_normalizer_centralizer_map_eq hp hp2 π hkp hk2 hS hSinj
    (IsPGroup.of_bot) bot_le (fun d hd => by rw [Subgroup.mem_bot.1 hd, one_mul, mul_one]) hm
  exact ⟨g, hg.1, hgh⟩

theorem map_centralizer_inf_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (π : H →* M)
    (hπ : Function.Surjective π) (hkp : ¬ p ∣ Nat.card π.ker) (hk2 : ¬ 2 ∣ Nat.card π.ker)
    {S : Subgroup H} (hS : IsPGroup 2 S) (hSinj : Function.Injective (π.comp S.subtype))
    {y : H} (hy : IsPGroup p (Subgroup.zpowers y)) (hyS : y ∈ Subgroup.normalizer (S : Set H)) :
    (Subgroup.centralizer ({y} : Set H) ⊓ Subgroup.normalizer (S : Set H)).map π =
      Subgroup.centralizer ({π y} : Set M) ⊓
        Subgroup.normalizer ((S.map π : Subgroup M) : Set M) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hgy : g ∈ Subgroup.centralizer ({y} : Set H) := hg.1
    have hgS : g ∈ Subgroup.normalizer (S : Set H) := hg.2
    refine ⟨?_, Subgroup.le_normalizer_map π ⟨g, hgS, rfl⟩⟩
    show π g ∈ Subgroup.centralizer ({π y} : Set M)
    rw [Subgroup.mem_centralizer_singleton_iff] at hgy ⊢
    rw [← map_mul, ← map_mul, hgy]
  · intro m hm
    have hmy : m ∈ Subgroup.centralizer ({π y} : Set M) := hm.1
    have hmS : m ∈ Subgroup.normalizer ((S.map π : Subgroup M) : Set M) := hm.2
    obtain ⟨k, rfl⟩ := hπ m
    rw [Subgroup.mem_centralizer_singleton_iff] at hmy
    obtain ⟨n, hn, hkn⟩ := exists_mem_ker_mul_commute hp π hkp hy hmy
    have hπn : π (k * n) = π k := by rw [map_mul, MonoidHom.mem_ker.1 hn, mul_one]
    have hhD : ∀ d ∈ Subgroup.zpowers y, d * (k * n) = (k * n) * d := by
      intro d hd
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hd
      exact ((Commute.zpow_left (show Commute y (k * n) from hkn.symm) i)).eq
    obtain ⟨g, ⟨hgS, hgD⟩, hgh⟩ := exists_mem_normalizer_centralizer_map_eq hp hp2 π hkp hk2
      hS hSinj hy (Subgroup.zpowers_le.2 hyS) hhD (by rw [hπn]; exact hmS)
    refine ⟨g, ⟨?_, hgS⟩, hgh.trans hπn⟩
    show g ∈ Subgroup.centralizer ({y} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hgD y (Subgroup.mem_zpowers y)).symm

theorem exists_pGroup_lift_normalizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (π : H →* M)
    (hπ : Function.Surjective π) (hkp : ¬ p ∣ Nat.card π.ker) (hk2 : ¬ 2 ∣ Nat.card π.ker)
    {S : Subgroup H} (hS : IsPGroup 2 S) (hSinj : Function.Injective (π.comp S.subtype))
    {B : Subgroup M} (hB : IsPGroup p B)
    (hBN : B ≤ Subgroup.normalizer ((S.map π : Subgroup M) : Set M)) :
    ∃ W : Subgroup H, W ≤ Subgroup.normalizer (S : Set H) ∧ IsPGroup p W ∧ W.map π = B ∧
      Function.Injective (π.comp W.subtype) := by
  set N : Subgroup H := Subgroup.normalizer (S : Set H) with hN
  set ψ : ↥N →* M := π.comp N.subtype with hψ
  have hrange : ψ.range = Subgroup.normalizer ((S.map π : Subgroup M) : Set M) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
    exact map_normalizer_eq hp hp2 π hπ hkp hk2 hS hSinj
  have hkψ : ¬ p ∣ Nat.card ψ.ker := fun h => hkp (h.trans (CatB.card_ker_comp_subtype_dvd π N))
  obtain ⟨W', hW'p, hW'map, -⟩ := CatB.exists_pSubgroup_lift hp ψ hkψ hB (hrange ▸ hBN)
  refine ⟨W'.map N.subtype, Subgroup.map_subtype_le _, hW'p.map _, ?_,
    CatB.injective_comp_subtype hp π hkp (hW'p.map _)⟩
  rw [Subgroup.map_map]
  exact hW'map

end Frattini

end CFSG.LocalAnalysis.GLTheoremA.H301
