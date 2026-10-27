module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointAutomizer
import CFSG.LocalAnalysis.RankFourTheoremC.PPointCover
import CFSG.LocalAnalysis.RankFourTheoremC.PPointSemilinear
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools
  CFSG.PreuniquenessRankFour.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

namespace BorelData3

variable {P : Sylow 3 G} {M : Subgroup G} {x : G} {n : ℕ} {f : GaloisField 3 n → G}
  {W : Subgroup G}

def commQK (hB : BorelData3 P M x f W) (O Y : Subgroup G)
    (hQO : hB.QK ≤ normalizer (O : Set G)) : Subgroup G where
  carrier := {g | g ∈ hB.QK ∧ ∀ i ∈ Y, i ^ 2 = 1 → g * i * g⁻¹ * i⁻¹ ∈ O}
  mul_mem' := by
    rintro g g' ⟨hg, hgi⟩ ⟨hg', hg'i⟩
    refine ⟨hB.QK.mul_mem hg hg', fun i hi hi2 => ?_⟩
    have e : g * g' * i * (g * g')⁻¹ * i⁻¹ =
        (g * (g' * i * g'⁻¹ * i⁻¹) * g⁻¹) * (g * i * g⁻¹ * i⁻¹) := by group
    rw [e]
    exact O.mul_mem ((mem_normalizer_iff.mp (hQO hg) _).mp (hg'i i hi hi2)) (hgi i hi hi2)
  one_mem' := ⟨hB.QK.one_mem, fun i _ _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hgi⟩
    refine ⟨hB.QK.inv_mem hg, fun i hi hi2 => ?_⟩
    have e : g⁻¹ * i * (g⁻¹)⁻¹ * i⁻¹ = g⁻¹ * (g * i * g⁻¹ * i⁻¹)⁻¹ * g := by group
    rw [e]
    have := (mem_normalizer_iff.mp (hQO (hB.QK.inv_mem hg)) _).mp (O.inv_mem (hgi i hi hi2))
    simpa [mul_assoc] using this

theorem normalizer_le_of_normal (hB : BorelData3 P M x f W) {O : Subgroup G}
    (hwc : ∀ g : G, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x)
    (hO3 : ¬ 3 ∣ Nat.card O) (hO2 : 2 ∣ Nat.card O)
    (hOM : M ≤ normalizer (O : Set G)) (hOle : O ≤ M)
    (hQM : hB.QK ≤ M) (hRM : M ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G))
    (hCM : centralizer (hB.QK : Set G) ≤ M) (hxM : x ∈ M)
    (hD1 : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 3 (H ⊓ M) → H ≤ M)
    {t₀ : GaloisField 3 n} (ht₀ : t₀ ≠ 0) {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYM : Y ≤ M)
    (hUY : plane x f t₀ ≤ normalizer (Y : Set G)) (hYO : IsSylowOf 2 (Y ⊓ O) O) :
    normalizer (Y : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQO : hB.QK ≤ normalizer (O : Set G) := hQM.trans hOM
  have hY1 : Y ≠ ⊥ := by
    intro hbot
    have h1 := hYO.card_eq
    rw [hbot, bot_inf_eq, Subgroup.card_bot] at h1
    have h2 : (Nat.card O).factorization 2 ≠ 0 := by
      have hpos : Nat.card O ≠ 0 := Nat.card_pos.ne'
      have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hpos).mp hO2
      omega
    have : 2 ^ (Nat.card O).factorization 2 = 1 := h1.symm
    have h3 : (Nat.card O).factorization 2 = 0 := by
      by_contra hne
      have := Nat.one_lt_two_pow hne
      omega
    exact h2 h3
  have hY₁ne : involClosure Y ≠ ⊥ := involClosure_ne_bot hY2 hY1
  choose ψ hψ using fun i : Y => exists_acts (hB := hB) hRM hQO (hYM i.2)
  have hψadd : ∀ i : Y, ∀ s t, ψ i (s + t) = ψ i s + ψ i t := fun i =>
    (hψ i).map_add hO3 hQO
  have hψinj : ∀ i : Y, Function.Injective (ψ i) := fun i =>
    (hψ i).injective hO3 hQO (hOM (hYM i.2))
  let ψe : Y → (GaloisField 3 n ≃+ GaloisField 3 n) := fun i =>
    AddEquiv.ofBijective (AddMonoidHom.mk' (ψ i) (hψadd i))
      ⟨hψinj i, Finite.surjective_of_injective (hψinj i)⟩
  have hψe : ∀ i t, ψe i t = ψ i t := fun i t => rfl
  set Ψ : Set (GaloisField 3 n ≃+ GaloisField 3 n) :=
    {φ | ∃ i : Y, (i : G) ^ 2 = 1 ∧ φ = ψe i} with hΨ
  have hFcard : Nat.card (GaloisField 3 n) = 3 ^ n :=
    GaloisField.card 3 n (by have := hB.three_le; omega)
  have hfix : ∀ i : Y, (i : G) ^ 2 = 1 → ψ i t₀ = t₀ := by
    intro i hi2
    obtain ⟨o, ho, hio⟩ := hψ i t₀
    have hu : f t₀ ∈ normalizer (Y : Set G) := hUY (f_mem_plane x f t₀)
    set c : G := f t₀ * i * (f t₀)⁻¹ * (i : G)⁻¹ with hc
    have hcY : c ∈ Y := Y.mul_mem ((mem_normalizer_iff.mp hu i).mp i.2) (Y.inv_mem i.2)
    have hcR : c ∈ hB.QK ⊔ O := by
      have e : c = f t₀ * (f (ψ i t₀) * o)⁻¹ := by
        rw [← hio, hc]; group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hB.f_mem_QK t₀)) (Subgroup.inv_mem _ ?_)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hB.f_mem_QK _)) (Subgroup.mem_sup_right ho)
    have hc3 : c ^ 3 ∈ O := hB.pow_three_mem_QK_sup hQO hcR
    have hcO : c ∈ O := by
      obtain ⟨k, hk⟩ := hY2 ⟨c, hcY⟩
      have hord : orderOf c ∣ 2 ^ k :=
        orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
      have hcop : Nat.Coprime 3 (orderOf c) :=
        Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right _ (by norm_num))
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      rw [← hm]
      exact O.pow_mem hc3 m
    have hcf : (i : G) * f t₀ * (i : G)⁻¹ = c⁻¹ * f t₀ := by rw [hc]; group
    have : f (ψ i t₀) * o = f t₀ * ((f t₀)⁻¹ * c⁻¹ * f t₀) := by
      rw [← hio, hcf]; group
    have ho' : (f t₀)⁻¹ * c⁻¹ * f t₀ ∈ O := by
      have := (mem_normalizer_iff.mp (hQO (hB.QK.inv_mem (hB.f_mem_QK t₀))) c⁻¹).mp (O.inv_mem hcO)
      simpa using this
    exact hB.eq_of_f_mul_mem hO3 ho ho' hQO this
  have hn3 : 3 ≤ n := hB.three_le
  obtain ⟨w, hwfix, hw0, hwv, hwv'⟩ := exists_fixed_not_mem_line (F := GaloisField 3 n) hFcard hn3
    Ψ (by
      rintro φ ⟨i, hi2, rfl⟩ t
      exact (hψ i).involutive hO3 hQO (hOM (hYM i.2)) (by rw [← pow_two]; exact hi2) t)
    (by
      rintro φ ⟨i, hi2, rfl⟩ a
      exact Acts.squares hB hwc hO3 hOM hOle hQM hRM hCM (hYM i.2) (hψ i) a)
    ht₀ (by
      rintro φ ⟨i, hi2, rfl⟩
      exact hfix i hi2)
  have hwψ : ∀ i : Y, (i : G) ^ 2 = 1 → ψ i w = w := fun i hi2 => hwfix (ψe i) ⟨i, hi2, rfl⟩
  have hmemA : ∀ s : GaloisField 3 n, (∀ i : Y, (i : G) ^ 2 = 1 → ψ i s = s) →
      f s ∈ hB.commQK O Y hQO := by
    intro s hs
    refine ⟨hB.f_mem_QK s, fun i hiY hi2 => ?_⟩
    obtain ⟨o, ho, h⟩ := hψ ⟨i, hiY⟩ s
    have h' : i * f s * i⁻¹ = f s * o := by
      have := h
      rw [hs ⟨i, hiY⟩ hi2] at this
      exact this
    have e : f s * i * (f s)⁻¹ * i⁻¹ = f s * o⁻¹ * (f s)⁻¹ := by
      calc f s * i * (f s)⁻¹ * i⁻¹ = f s * (i * f s * i⁻¹)⁻¹ := by group
        _ = f s * (f s * o)⁻¹ := by rw [h']
        _ = f s * o⁻¹ * (f s)⁻¹ := by group
    rw [e]
    exact (mem_normalizer_iff.mp (hQO (hB.f_mem_QK s)) _).mp (O.inv_mem ho)
  have hft0 : f t₀ ≠ 1 := fun h => ht₀ (hB.f_inj (h.trans hB.f_zero.symm))
  have hnot : f w ∉ zpowers (f t₀) := by
    intro hmem
    rcases mem_zpowers_of_pow_three (hB.f_pow_three t₀) hmem with h | h | h
    · exact hw0 (hB.f_inj (h.trans hB.f_zero.symm))
    · exact hwv (hB.f_inj h)
    · exact hwv' (hB.f_inj (by rw [hB.f_neg]; exact h))
  have hcommB : ∀ e ∈ zpowers (f t₀), e * f w = f w * e := by
    intro e he
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute (f t₀) (f w) from
      hB.QK_comm (hB.f_mem_QK _) (hB.f_mem_QK _)) k).eq
  have hB9 : Nat.card (zpowers (f t₀) ⊔ zpowers (f w) : Subgroup G) = 3 ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers (f t₀))
      (hB.f_pow_three w) hnot hcommB, Nat.card_zpowers,
      orderOf_eq_prime (hB.f_pow_three t₀) hft0]
    norm_num
  have hBA : (zpowers (f t₀) ⊔ zpowers (f w) : Subgroup G) ≤ hB.commQK O Y hQO :=
    sup_le (zpowers_le.mpr (hmemA t₀ hfix)) (zpowers_le.mpr (hmemA w hwψ))
  have hA9 : 9 ≤ Nat.card (hB.commQK O Y hQO) := by
    have := Subgroup.card_le_of_le hBA
    rw [hB9] at this
    omega
  have hRO : (hB.QK ⊔ O : Subgroup G) ≤ normalizer (O : Set G) :=
    sup_le hQO Subgroup.le_normalizer
  have hYR : Y ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G) := hYM.trans hRM
  have hYO' : Y ≤ normalizer (O : Set G) := hYM.trans hOM
  have hxR : x ∉ (hB.QK ⊔ O : Subgroup G) := by
    intro hxr
    obtain ⟨t, o, ho, hxo⟩ := (hB.mem_QK_sup_iff hQO).mp hxr
    have hco : Commute ((f t)⁻¹) x := (show Commute (f t) x from hB.f_comm t).inv_left
    have ho' : o = (f t)⁻¹ * x := by rw [hxo]; group
    have ho3 : o ^ 3 = 1 := by
      rw [ho', hco.mul_pow, inv_pow, hB.f_pow_three, hB.x_pow]
      simp
    have ho1 : o = 1 := by
      have hd : orderOf o ∣ 3 := orderOf_dvd_of_pow_eq_one ho3
      have hd2 : orderOf o ∣ Nat.card O := by
        have := orderOf_dvd_natCard (⟨o, ho⟩ : O)
        rwa [Subgroup.orderOf_mk] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact absurd (h ▸ hd2) hO3
    rw [ho1, mul_one] at hxo
    exact hB.f_ne t hxo.symm
  have hxc : ∀ r ∈ (hB.QK ⊔ O : Subgroup G), x * r * x⁻¹ * r⁻¹ ∈ O := by
    intro r hr
    obtain ⟨t, o, ho, rfl⟩ := (hB.mem_QK_sup_iff hQO).mp hr
    have hxf : x * f t * x⁻¹ = f t := by
      have := hB.f_comm t
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have e : x * (f t * o) * x⁻¹ * (f t * o)⁻¹ = f t * (x * o * x⁻¹ * o⁻¹) * (f t)⁻¹ := by
      calc x * (f t * o) * x⁻¹ * (f t * o)⁻¹ = (x * f t * x⁻¹) * (x * o * x⁻¹) * o⁻¹ * (f t)⁻¹ := by
            group
        _ = f t * (x * o * x⁻¹ * o⁻¹) * (f t)⁻¹ := by rw [hxf]; group
    rw [e]
    exact (mem_normalizer_iff.mp (hQO (hB.f_mem_QK t)) _).mp
      (O.mul_mem ((mem_normalizer_iff.mp (hOM hxM) o).mp ho) (O.inv_mem ho))
  obtain ⟨E, hEN, hER, hEel, hE27⟩ := exists_elemAbelian_three_normalizing_involClosure
    (O := O) (R := hB.QK ⊔ O) (Y := Y) (A := hB.commQK O Y hQO) (x := x) le_sup_right hRO hYR
    hYO' hO3 (fun r hr => hB.pow_three_mem_QK_sup hQO hr)
    (fun r hr r' hr' => hB.comm_mem_QK_sup hQO hr hr') hY2 hYO hB.x_pow hxR (hRM hxM) hxc
    (hUY (x_mem_plane x f t₀))
    (fun a ha => Subgroup.mem_sup_left ha.1) (by
      rw [eq_bot_iff]
      rintro g ⟨hgA, hgO⟩
      have := hB.QK_inf_eq_bot hO3 hQO
      exact (this.le ⟨hgA.1, hgO⟩)) hA9 (fun a ha i hi hi2 => ha.2 i hi hi2)
  have hEM : E ≤ M := hER.trans (sup_le (sup_le hQM hOle) (zpowers_le.mpr hxM))
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEel.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hrank : 3 ≤ CFSG.Open.pRank 3 (normalizer (involClosure Y : Set G) ⊓ M) :=
    hk3.trans (le_csSup (pRank_bddAbove 3 Nat.prime_three _) ⟨E, le_inf hEN hEM, hEel, hk⟩)
  have hTL : IsTwoLocal (normalizer (involClosure Y : Set G)) :=
    ⟨involClosure Y, hY₁ne, hY2.to_le (involClosure_le Y), rfl⟩
  have hNM := hD1 _ hTL hrank
  intro g hg
  exact hNM (mem_normalizer_involClosure hg)

end BorelData3

end CFSG.LocalAnalysis.RankFourTheoremC
