module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.Basic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.LemmaR.Hyp
import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Shape

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG.EvenSporadicStandard.HSStd.InvCent CFSG.EvenSporadicStandard.SolomonRed

variable {G : Type*} [Group G] {B : Type*} [Group B]

@[expose] def tC (t : G) : ↥(centralizer ({t} : Set G)) :=
  ⟨t, mem_centralizer_singleton_iff.2 rfl⟩

structure ModData (t : G) (B₀ : Subgroup B)
    (ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B) : Prop where
  t_sq : t * t = 1
  t_ne : t ≠ 1
  surj : Function.Surjective ψ
  odd : Odd (Nat.card ψ.ker)
  hR : RHyp B B₀

@[expose] def phi {t : G} (ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B) :
    ↥(centralizer ({t} : Set G)) →* B :=
  (MonoidHom.snd _ _).comp ψ

@[expose] def imgOf {t : G} (ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B)
    (Y : Subgroup G) : Subgroup B :=
  (Y.subgroupOf (centralizer ({t} : Set G))).map (phi ψ)

variable {t : G} {B₀ : Subgroup B}
  {ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B}

private theorem phi_surjective (h : ModData t B₀ ψ) : Function.Surjective (phi ψ) := by
  intro b
  obtain ⟨c, hc⟩ := h.surj (1, b)
  exact ⟨c, by simp [phi, hc]⟩

theorem mem_imgOf {Y : Subgroup G} {b : B} :
    b ∈ imgOf ψ Y ↔ ∃ y ∈ Y, ∃ hy : y ∈ centralizer ({t} : Set G), phi ψ ⟨y, hy⟩ = b := by
  simp only [imgOf, Subgroup.mem_map]
  constructor
  · rintro ⟨c, hc, hcb⟩
    exact ⟨c.1, Subgroup.mem_subgroupOf.1 hc, c.2, hcb⟩
  · rintro ⟨y, hy, hyc, hyb⟩
    exact ⟨⟨y, hyc⟩, Subgroup.mem_subgroupOf.2 hy, hyb⟩

theorem imgOf_mono {Y Y' : Subgroup G} (h : Y ≤ Y') : imgOf ψ Y ≤ imgOf ψ Y' := by
  intro b hb
  rw [mem_imgOf] at hb ⊢
  obtain ⟨y, hy, hyc, hyb⟩ := hb
  exact ⟨y, h hy, hyc, hyb⟩

theorem imgOf_eq_bot_iff {Y : Subgroup G} :
    imgOf ψ Y = ⊥ ↔ ∀ y ∈ Y, ∀ hy : y ∈ centralizer ({t} : Set G), phi ψ ⟨y, hy⟩ = 1 := by
  constructor
  · intro h y hy hyc
    have hmem : phi ψ ⟨y, hyc⟩ ∈ imgOf ψ Y := by
      rw [mem_imgOf]
      exact ⟨y, hy, hyc, rfl⟩
    rwa [h, Subgroup.mem_bot] at hmem
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    rw [mem_imgOf] at hb
    obtain ⟨y, hy, hyc, hyb⟩ := hb
    rw [← hyb]
    exact h y hy hyc

namespace ModData

theorem phi_tC (h : ModData t B₀ ψ) : phi ψ (tC t) = 1 := by
  show (ψ (tC t)).2 = 1
  refine h.hR.center (ψ (tC t)).2 fun b => ?_
  obtain ⟨c, hc⟩ := h.surj (1, b)
  have hcomm : c * tC t = tC t * c :=
    Subtype.ext (mem_centralizer_singleton_iff.1 c.2)
  have h2 := congrArg ψ hcomm
  rw [map_mul, map_mul, hc] at h2
  exact congrArg Prod.snd h2

theorem fst_psi_tC_ne_one [Finite G] (h : ModData t B₀ ψ) : (ψ (tC t)).1 ≠ 1 := by
  intro h1
  have hker : tC t ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact Prod.ext h1 (phi_tC h)
  have hpow : tC t ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    apply Subtype.ext
    simpa [tC] using h.t_sq
  have h1' := eq_one_of_mem_odd_of_pow_two_pow_eq_one (G := ↥(centralizer ({t} : Set G)))
    h.odd hker hpow
  exact h.t_ne (by simpa [tC] using congrArg Subtype.val h1')

theorem mem_ker_or [Finite G] (h : ModData t B₀ ψ) {c : ↥(centralizer ({t} : Set G))}
    (hc : phi ψ c = 1) : c ∈ ψ.ker ∨ tC t * c ∈ ψ.ker := by
  have hz2 : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by decide
  have ha₀ : (ψ (tC t)).1 ≠ 1 := fst_psi_tC_ne_one h
  have hfst : (ψ (tC t)).2 = 1 := phi_tC h
  have hc2 : (ψ c).2 = 1 := hc
  have hψc : ψ c = ((ψ c).1, (1 : B)) := Prod.ext rfl hc2
  by_cases ha : (ψ c).1 = 1
  · left
    rw [MonoidHom.mem_ker]
    exact Prod.ext ha hc2
  · right
    have heq : (ψ c).1 = (ψ (tC t)).1 := z2_eq_of_ne_one ha ha₀
    rw [MonoidHom.mem_ker, map_mul]
    have hψc' : ψ c = ((ψ (tC t)).1, (1 : B)) := by rw [hψc, heq]
    rw [hψc']
    exact Prod.ext (hz2 _) (by simp [hfst])

theorem eq_one_or_eq_t [Finite G] (h : ModData t B₀ ψ) {c : G}
    (hc : c ∈ centralizer ({t} : Set G)) (hφ : phi ψ ⟨c, hc⟩ = 1) {k : ℕ} (hk : c ^ 2 ^ k = 1) :
    c = 1 ∨ c = t := by
  let c' : ↥(centralizer ({t} : Set G)) := ⟨c, hc⟩
  have htC2 : (tC t) ^ 2 = 1 := by
    rw [pow_two]
    apply Subtype.ext
    simpa [tC] using h.t_sq
  have htC2' : tC t * tC t = 1 := by rw [← pow_two]; exact htC2
  have hc'pow : c' ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa [c'] using hk
  rcases mem_ker_or h (c := c') hφ with hmem | hmem
  · left
    have h1 := eq_one_of_mem_odd_of_pow_two_pow_eq_one (G := ↥(centralizer ({t} : Set G)))
      h.odd hmem hc'pow
    exact congrArg Subtype.val h1
  · right
    have hcomm : Commute (tC t) c' :=
      Subtype.ext (mem_centralizer_singleton_iff.1 hc).symm
    have hpow2 : (tC t * c') ^ 2 = c' ^ 2 := by
      rw [hcomm.mul_pow, htC2, one_mul]
    have hpow : (tC t * c') ^ 2 ^ (k + 1) = 1 := by
      have h1 : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
      rw [h1, pow_mul', hpow2, ← pow_mul c' 2 (2 ^ k), pow_mul', hc'pow, one_pow]
    have h1 := eq_one_of_mem_odd_of_pow_two_pow_eq_one (G := ↥(centralizer ({t} : Set G)))
      h.odd hmem hpow
    have hc't : c' = tC t := by
      have h2 := congrArg (fun x : ↥(centralizer ({t} : Set G)) => tC t * x) h1
      rw [mul_one] at h2
      rwa [← mul_assoc, htC2', one_mul] at h2
    exact congrArg Subtype.val hc't

theorem le_zpowers_of_normal_two [Finite G] (h : ModData t B₀ ψ)
    {P : Subgroup ↥(centralizer ({t} : Set G))} [P.Normal] (hP : IsPGroup 2 P) :
    ∀ p ∈ P, (p : G) ∈ zpowers t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite B := Finite.of_surjective (phi ψ) (phi_surjective h)
  let N : Subgroup B := P.map (phi ψ)
  have hNnormal : N.Normal := (inferInstance : P.Normal).map (phi ψ) (phi_surjective h)
  have hNpgroup : IsPGroup 2 N := hP.map (phi ψ)
  have hNbot : N = ⊥ := by
    by_contra hne
    have hle : B₀ ≤ N := h.hR.min N hNnormal hne
    exact not_isPGroup_of_simple_nonabelian h.hR.simple h.hR.nonab (hNpgroup.to_le hle)
  intro p hp
  have hφp : phi ψ p = 1 := by
    have hmem : phi ψ p ∈ N := ⟨p, hp, rfl⟩
    rwa [hNbot, Subgroup.mem_bot] at hmem
  obtain ⟨k, hk⟩ := hP ⟨p, hp⟩
  have hkp : (p : G) ^ 2 ^ k = 1 := by
    have h2 := congrArg (fun x : P => (x : G)) hk
    simpa using h2
  rcases eq_one_or_eq_t h p.2 hφp hkp with h1 | ht
  · rw [h1]; exact Subgroup.one_mem _
  · rw [ht]; exact Subgroup.mem_zpowers t

theorem not_four_dvd_natCard [Finite G] (h : ModData t B₀ ψ) {Y : Subgroup G}
    (hY : imgOf ψ Y = ⊥) (hYC : Y ≤ centralizer ({t} : Set G)) : ¬ 4 ∣ Nat.card Y := by
  classical
  intro hfour
  have hdvd : 2 ^ 2 ∣ Nat.card Y := by simpa using hfour
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) hdvd
  have hK4 : Nat.card K = 4 := by rw [hKcard]; norm_num
  let f : K → G := fun x => ((x : Y) : G)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have hf_mem : ∀ x : K, f x = 1 ∨ f x = t := by
    intro x
    have hxpow : f x ^ 2 ^ 2 = 1 := by
      have hcard := pow_card_eq_one' (x := x)
      rw [hK4] at hcard
      have h2 : (((x : K) : Y) : G) ^ 4 = 1 := by
        simpa using congrArg (fun y : K => ((y : Y) : G)) hcard
      simpa [f] using h2
    have hφx : phi ψ ⟨f x, hYC (x : Y).2⟩ = 1 := by
      have hmem : phi ψ ⟨f x, hYC (x : Y).2⟩ ∈ imgOf ψ Y := by
        rw [mem_imgOf]
        exact ⟨f x, (x : Y).2, hYC (x : Y).2, rfl⟩
      rwa [hY, Subgroup.mem_bot] at hmem
    exact eq_one_or_eq_t h (hYC (x : Y).2) hφx hxpow
  let g : K → Fin 2 := fun x => if f x = 1 then 0 else 1
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have hfx := hf_mem x
    have hfy := hf_mem y
    have hfxy : f x = f y := by
      by_cases hx1 : f x = 1
      · have hgy : g y = 0 := by rw [← hxy]; simp [g, hx1]
        by_cases hy1 : f y = 1
        · rw [hx1, hy1]
        · have hgy1 : g y = 1 := by simp [g, hy1]
          exact absurd (hgy.symm.trans hgy1) (by decide)
      · have hxt : f x = t := hfx.resolve_left hx1
        have hgx : g x = 1 := by simp [g, hx1]
        have hgy : g y = 1 := by rw [← hxy]; exact hgx
        by_cases hy1 : f y = 1
        · have hgy0 : g y = 0 := by simp [g, hy1]
          exact absurd (hgy.symm.trans hgy0) (by decide)
        · rw [hxt, hfy.resolve_left hy1]
    exact hf_inj hfxy
  have hle := Nat.card_le_card_of_injective g hg_inj
  rw [Nat.card_fin] at hle
  omega

theorem imgOf_eq_bot_or_le (h : ModData t B₀ ψ) {Y : Subgroup G}
    (hY : ∀ c ∈ centralizer ({t} : Set G), ∀ y ∈ Y, c * y * c⁻¹ ∈ Y) :
    imgOf ψ Y = ⊥ ∨ B₀ ≤ imgOf ψ Y := by
  have hNnormal : (imgOf ψ Y).Normal := by
    refine ⟨fun n hn b => ?_⟩
    rw [mem_imgOf] at hn ⊢
    obtain ⟨y, hyY, hyC, hyb⟩ := hn
    obtain ⟨c, hc⟩ := phi_surjective h b
    have hcy : c.1 * y * c.1⁻¹ ∈ centralizer ({t} : Set G) :=
      mul_mem (mul_mem c.2 hyC) (inv_mem c.2)
    refine ⟨c.1 * y * c.1⁻¹, hY c.1 c.2 y hyY, hcy, ?_⟩
    change phi ψ (c * ⟨y, hyC⟩ * c⁻¹) = b * n * b⁻¹
    rw [map_mul, map_mul, map_inv, hc, hyb]
  by_cases hbot : imgOf ψ Y = ⊥
  · exact Or.inl hbot
  · exact Or.inr (h.hR.min (imgOf ψ Y) hNnormal hbot)

theorem false_of_decomposition (h : ModData t B₀ ψ) {M P Q : Subgroup G}
    (hM : ∀ c ∈ centralizer ({t} : Set G), ∀ y ∈ M, c * y * c⁻¹ ∈ M)
    (hMC : M ≤ centralizer ({t} : Set G)) (hP : P ≤ M) (hQ : Q ≤ M)
    (hPQ : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) (hdec : ∀ m ∈ M, ∃ p ∈ P, ∃ q ∈ Q, m = p * q)
    (hP1 : imgOf ψ P ≠ ⊥) (hQ1 : imgOf ψ Q ≠ ⊥) : False := by
  have hPM : imgOf ψ P ≤ imgOf ψ M := imgOf_mono hP
  have hQM : imgOf ψ Q ≤ imgOf ψ M := imgOf_mono hQ
  have hNne : imgOf ψ M ≠ ⊥ := by
    intro hbot
    exact hP1 (le_bot_iff.1 (hbot ▸ hPM))
  have hBM : B₀ ≤ imgOf ψ M := (imgOf_eq_bot_or_le h hM).resolve_left hNne
  have hPQimg : ∀ p ∈ imgOf ψ P, ∀ q ∈ imgOf ψ Q, p * q = q * p := by
    intro p hp q hq
    rw [mem_imgOf] at hp hq
    obtain ⟨p', hpP, hpC, hpEq⟩ := hp
    obtain ⟨q', hqQ, hqC, hqEq⟩ := hq
    rw [← hpEq, ← hqEq]
    have hcomm : (⟨p', hpC⟩ : ↥(centralizer ({t} : Set G))) * ⟨q', hqC⟩ =
        ⟨q', hqC⟩ * ⟨p', hpC⟩ := by
      apply Subtype.ext
      exact hPQ p' hpP q' hqQ
    calc phi ψ ⟨p', hpC⟩ * phi ψ ⟨q', hqC⟩
        = phi ψ (⟨p', hpC⟩ * ⟨q', hqC⟩) := (map_mul _ _ _).symm
      _ = phi ψ (⟨q', hqC⟩ * ⟨p', hpC⟩) := congrArg (phi ψ) hcomm
      _ = phi ψ ⟨q', hqC⟩ * phi ψ ⟨p', hpC⟩ := map_mul _ _ _
  have hMdec : ∀ m ∈ imgOf ψ M, ∃ p ∈ imgOf ψ P, ∃ q ∈ imgOf ψ Q, m = p * q := by
    intro m hm
    rw [mem_imgOf] at hm
    obtain ⟨m', hmM, hmC, hmEq⟩ := hm
    obtain ⟨p', hpP, q', hqQ, hpq⟩ := hdec m' hmM
    refine ⟨phi ψ ⟨p', hMC (hP hpP)⟩, ?_, phi ψ ⟨q', hMC (hQ hqQ)⟩, ?_, ?_⟩
    · rw [mem_imgOf]; exact ⟨p', hpP, hMC (hP hpP), rfl⟩
    · rw [mem_imgOf]; exact ⟨q', hqQ, hMC (hQ hqQ), rfl⟩
    · calc m = phi ψ ⟨m', hmC⟩ := hmEq.symm
        _ = phi ψ (⟨p', hMC (hP hpP)⟩ * ⟨q', hMC (hQ hqQ)⟩) :=
            congrArg (phi ψ) (Subtype.ext hpq)
        _ = phi ψ ⟨p', hMC (hP hpP)⟩ * phi ψ ⟨q', hMC (hQ hqQ)⟩ := map_mul _ _ _
  have hBn : ∀ m ∈ imgOf ψ M, ∀ b ∈ B₀, m * b * m⁻¹ ∈ B₀ :=
    fun m _ b hb => h.hR.normal.conj_mem b hb m
  rcases simple_le_or_le_of_decomposition h.hR.simple h.hR.nonab hBM hPM hQM hPQimg hMdec hBn
    with hleP | hleQ
  · apply hQ1
    rw [imgOf_eq_bot_iff]
    intro q hqQ hqC
    refine h.hR.eq_one_of_commute fun a ha => ?_
    have hqmem : phi ψ ⟨q, hqC⟩ ∈ imgOf ψ Q := by
      rw [mem_imgOf]; exact ⟨q, hqQ, hqC, rfl⟩
    exact (hPQimg a (hleP ha) (phi ψ ⟨q, hqC⟩) hqmem).symm
  · apply hP1
    rw [imgOf_eq_bot_iff]
    intro p hpP hpC
    refine h.hR.eq_one_of_commute fun a ha => ?_
    have hpmem : phi ψ ⟨p, hpC⟩ ∈ imgOf ψ P := by
      rw [mem_imgOf]; exact ⟨p, hpP, hpC, rfl⟩
    exact hPQimg (phi ψ ⟨p, hpC⟩) hpmem a (hleQ ha)

end ModData

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
