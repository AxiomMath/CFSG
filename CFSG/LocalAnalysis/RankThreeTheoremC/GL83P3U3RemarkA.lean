module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Layer
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponents
import CFSG.Walter.W67.CentralExt
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

structure Case2Data3 (p : ℕ) {Y : Type} [Group Y] [Finite Y] (P T D F : Subgroup Y) (x : Y) :
    Prop where
  prime : p.Prime
  three : p = 3
  core : primeComplementCore (G := Y) p = ⊥
  catalog : CatalogSimpleSections Y
  rank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3
  sylow : ∃ S : Sylow p Y, (S : Subgroup Y) = P
  pdata : PGroupData p P T D x
  torus : TorusProps p T F
  F_D : ∀ f ∈ F, ∀ d ∈ D, f * d * f⁻¹ = d
  series : ∃ N : Subgroup Y, CentSeries p (centralizer ({x} : Set Y)) P N
  wc : ∀ g : Y, (zpowers x).map (MulAut.conj g).toMonoidHom ≤ P →
    (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

theorem fact (h : Case2Data3 p P T D F x) : Fact p.Prime := ⟨h.prime⟩

theorem zOf_card (h : Case2Data3 p P T D F x) : Nat.card (zOf T) = p := by
  haveI := h.fact
  exact card_inf_centralizer_of_nonabelian_card_p_cube h.pdata.T_card h.pdata.T_nonab

theorem zOf_le (h : Case2Data3 p P T D F x) : zOf T ≤ T := inf_le_left

theorem commutator_mem (h : Case2Data3 p P T D F x) :
    ∀ a ∈ T, ∀ b ∈ T, a * b * a⁻¹ * b⁻¹ ∈ zOf T := by
  haveI := h.fact
  have hZ : Nat.card (center T) = p :=
    card_center_of_nonabelian_card_p_cube h.pdata.T_card h.pdata.T_nonab
  have hQ : Nat.card (T ⧸ center T) = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center T)
    rw [h.pdata.T_card, hZ] at h1
    apply Nat.eq_of_mul_eq_mul_right h.prime.pos
    rw [← h1]
    ring
  have hcomm : IsMulCommutative (T ⧸ center T) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ
  intro a ha b hb
  have key : (⟨a, ha⟩ : T) * ⟨b, hb⟩ * (⟨a, ha⟩ : T)⁻¹ * (⟨b, hb⟩ : T)⁻¹ ∈ center T := by
    rw [← QuotientGroup.eq_one_iff]
    have hab := hcomm.is_comm.comm (QuotientGroup.mk (⟨a, ha⟩ : T) : T ⧸ center T)
      (QuotientGroup.mk ⟨b, hb⟩)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hab
  refine Subgroup.mem_inf.mpr
    ⟨T.mul_mem (T.mul_mem (T.mul_mem ha hb) (T.inv_mem ha)) (T.inv_mem hb), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have := mem_center_iff.mp key ⟨s, hs⟩
  exact congrArg Subtype.val this

private theorem exists_mul_aux (h : Case2Data3 p P T D F x) :
    ∀ a ∈ P, ∃ t ∈ T, ∃ d ∈ D, a = t * d := by
  intro a ha
  have hP : P = T ⊔ D := h.pdata.sup_eq.symm
  let S : Subgroup Y :=
    { carrier := {a | ∃ t ∈ T, ∃ d ∈ D, a = t * d}
      mul_mem' := by
        rintro _ _ ⟨t, ht, d, hd, rfl⟩ ⟨t', ht', d', hd', rfl⟩
        refine ⟨t * t', T.mul_mem ht ht', d * d', D.mul_mem hd hd', ?_⟩
        have hc : d * t' = t' * d := (h.pdata.comm t' ht' d hd).symm
        calc t * d * (t' * d') = t * (d * t') * d' := by group
          _ = t * (t' * d) * d' := by rw [hc]
          _ = t * t' * (d * d') := by group
      one_mem' := ⟨1, T.one_mem, 1, D.one_mem, (one_mul 1).symm⟩
      inv_mem' := by
        rintro _ ⟨t, ht, d, hd, rfl⟩
        refine ⟨t⁻¹, T.inv_mem ht, d⁻¹, D.inv_mem hd, ?_⟩
        rw [mul_inv_rev]
        exact (h.pdata.comm t⁻¹ (T.inv_mem ht) d⁻¹ (D.inv_mem hd)).symm }
  have hle : T ⊔ D ≤ S :=
    sup_le (fun t ht => ⟨t, ht, 1, D.one_mem, (mul_one t).symm⟩)
      (fun d hd => ⟨1, T.one_mem, d, hd, (one_mul d).symm⟩)
  rw [hP] at ha
  exact hle ha

private theorem D_comm (h : Case2Data3 p P T D F x) : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
  haveI := h.pdata.D_cyc
  intro a ha b hb
  have := (IsCyclic.isMulCommutative (α := D)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem zOf_central (h : Case2Data3 p P T D F x) :
    ∀ z ∈ zOf T, ∀ a ∈ P, z * a = a * z := by
  intro z hz a ha
  obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_aux h a ha
  obtain ⟨hzT, hzC⟩ := Subgroup.mem_inf.mp hz
  have h1 : z * t = t * z := (Subgroup.mem_centralizer_iff.mp hzC t ht).symm
  have h2 : z * d = d * z := h.pdata.comm z hzT d hd
  calc z * (t * d) = (z * t) * d := by group
    _ = (t * z) * d := by rw [h1]
    _ = t * (z * d) := by group
    _ = t * (d * z) := by rw [h2]
    _ = t * d * z := by group

theorem exists_mul (h : Case2Data3 p P T D F x) : ∀ a ∈ P, ∃ t ∈ T, ∃ d ∈ D, a = t * d :=
  exists_mul_aux h

private theorem isPGroup_P (h : Case2Data3 p P T D F x) : IsPGroup p P := by
  obtain ⟨S, hS⟩ := h.sylow
  subst hS
  exact S.isPGroup'

theorem exists_pow_eq_one (h : Case2Data3 p P T D F x) : ∀ a ∈ P, ∃ k : ℕ, a ^ (p ^ k) = 1 := by
  intro a ha
  obtain ⟨k, hk⟩ := isPGroup_P h ⟨a, ha⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem x_ne_one (h : Case2Data3 p P T D F x) : x ≠ 1 := by
  intro hx
  have h1 := h.pdata.x_ord
  rw [hx, orderOf_one] at h1
  have h2 := h.prime.one_lt
  omega

private theorem mem_zpowers_aux (h : Case2Data3 p P T D F x) :
    ∀ d ∈ D, d ^ p = 1 → d ∈ zpowers x := by
  classical
  haveI := h.fact
  haveI : IsCyclic D := h.pdata.D_cyc
  haveI : Fintype D := Fintype.ofFinite D
  intro d hd hdp
  obtain ⟨x', hx'⟩ : ∃ x' : D, (x' : Y) = x := ⟨⟨x, h.pdata.x_mem⟩, rfl⟩
  have hx'ord : orderOf x' = p := by
    rw [← h.pdata.x_ord, ← hx', Subgroup.orderOf_coe]
  have hx'p : x' ^ p = 1 := by
    have := pow_orderOf_eq_one x'
    rwa [hx'ord] at this
  have hsub : (zpowers x' : Set D) ⊆ {a : D | a ^ p = 1} := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    show (x' ^ k) ^ p = 1
    calc (x' ^ k) ^ p = (x' ^ k) ^ (p : ℤ) := (zpow_natCast _ _).symm
      _ = x' ^ (k * p) := (zpow_mul _ _ _).symm
      _ = x' ^ ((p : ℤ) * k) := by rw [mul_comm]
      _ = (x' ^ (p : ℤ)) ^ k := zpow_mul _ _ _
      _ = 1 := by rw [zpow_natCast, hx'p, one_zpow]
  have hfin : ({a : D | a ^ p = 1} : Set D).Finite := Set.toFinite _
  have hcard1 : Nat.card ({a : D | a ^ p = 1} : Set D) ≤ p := by
    have h1 : ({a : D | a ^ p = 1} : Set D) =
        ↑(Finset.univ.filter (fun a : D => a ^ p = 1)) := by
      ext a
      simp
    rw [h1, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    exact IsCyclic.card_pow_eq_one_le h.prime.pos
  have hcard2 : p ≤ Nat.card (zpowers x' : Set D) := by
    have : Nat.card (zpowers x') = p := by rw [Nat.card_zpowers, hx'ord]
    exact this.ge
  have heq : (zpowers x' : Set D) = {a : D | a ^ p = 1} :=
    Set.Finite.eq_of_subset_of_card_le hfin hsub (hcard1.trans hcard2)
  have hdmem : (⟨d, hd⟩ : D) ∈ zpowers x' := by
    have h1 : (⟨d, hd⟩ : D) ∈ ({a : D | a ^ p = 1} : Set D) := by
      show (⟨d, hd⟩ : D) ^ p = 1
      exact Subtype.ext (by simpa using hdp)
    rw [← heq] at h1
    exact h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdmem
  have h2 := congrArg Subtype.val hk
  simp only [Subgroup.coe_zpow, hx'] at h2
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩

theorem x_mem_of_ne_bot (h : Case2Data3 p P T D F x) :
    ∀ C : Subgroup Y, C ≤ D → C ≠ ⊥ → x ∈ C := by
  haveI := h.fact
  intro C hCD hC
  have hCP : C ≤ P := hCD.trans h.pdata.D_le
  have hCp : IsPGroup p C :=
    (isPGroup_P h).of_injective (Subgroup.inclusion hCP) (Subgroup.inclusion_injective hCP)
  haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC
  obtain ⟨n, hn, hcard⟩ := hCp.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card C := by
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hcY : orderOf (c : Y) = p := by
    rw [Subgroup.orderOf_coe]
    exact hc
  have hcp : (c : Y) ^ p = 1 := by
    have := pow_orderOf_eq_one (c : Y)
    rwa [hcY] at this
  have hcx : (c : Y) ∈ zpowers x := mem_zpowers_aux h (c : Y) (hCD c.2) hcp
  have hle : zpowers (c : Y) ≤ zpowers x := Subgroup.zpowers_le.mpr hcx
  have hcard' : Nat.card (zpowers x) ≤ Nat.card (zpowers (c : Y)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hcY, h.pdata.x_ord]
  have heq : zpowers (c : Y) = zpowers x := Subgroup.eq_of_le_of_card_ge hle hcard'
  have hxc : x ∈ zpowers (c : Y) := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.mpr c.2) hxc

theorem mem_zpowers_of_pow_eq_one (h : Case2Data3 p P T D F x) :
    ∀ d ∈ D, d ^ p = 1 → d ∈ zpowers x :=
  mem_zpowers_aux h

theorem P_le_centralizer (h : Case2Data3 p P T D F x) : P ≤ centralizer ({x} : Set Y) := by
  intro a ha
  obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_aux h a ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  have h1 : x * t = t * x := (h.pdata.comm t ht x h.pdata.x_mem).symm
  have h2 : x * d = d * x := D_comm h x h.pdata.x_mem d hd
  calc x * (t * d) = (x * t) * d := by group
    _ = (t * x) * d := by rw [h1]
    _ = t * (x * d) := by group
    _ = t * (d * x) := by rw [h2]
    _ = t * d * x := by group

theorem T_inf_zpowers (h : Case2Data3 p P T D F x) : T ⊓ zpowers x = ⊥ := by
  have hz : zpowers x ≤ D := Subgroup.zpowers_le.mpr h.pdata.x_mem
  rw [eq_bot_iff, ← h.pdata.inf_eq]
  exact inf_le_inf_left T hz

theorem F_mem_normalizer_P (h : Case2Data3 p P T D F x) :
    ∀ f ∈ F, ∀ a ∈ P, f * a * f⁻¹ ∈ P := by
  intro f hf a ha
  obtain ⟨t, ht, d, hd, rfl⟩ := exists_mul_aux h a ha
  have h1 : f * (t * d) * f⁻¹ = (f * t * f⁻¹) * (f * d * f⁻¹) := by group
  rw [h1, h.F_D f hf d hd]
  exact P.mul_mem (h.pdata.T_le (h.torus.F_T f hf t ht)) (h.pdata.D_le hd)

theorem F_fixed (h : Case2Data3 p P T D F x) :
    ∀ z ∈ zOf T, (∀ f ∈ F, f * z * f⁻¹ = z) → z = 1 := by
  intro z hz hfix
  have hnd : ¬ p ∣ 2 := by
    intro hd
    have h1 := Nat.le_of_dvd (by norm_num) hd
    have h2 := h.three
    omega
  obtain ⟨f, hf, hfz⟩ := h.torus.onto z hz 2 hnd
  rw [hfix f hf] at hfz
  have h3 : z * z = z * 1 := by
    rw [mul_one, ← pow_two]
    exact hfz.symm
  exact mul_left_cancel h3

end Case2Data3

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

theorem le_pCore_of_forall_le_centralizer (h : Case2Data3 p P T D F x)
    (hT : ∀ L : Subgroup Y, IsComponentOf L ⊤ → T ≤ centralizer (L : Set Y)) :
    T ≤ CFSG.pCore p Y := by
  haveI : Fact p.Prime := h.fact
  haveI hOn : (CFSG.pCore p Y).Normal := CFSG.pCore_normal
  have hTE : T ≤ centralizer (CFSG.layer Y : Set Y) := by
    have hlay : CFSG.layer Y ≤ centralizer (T : Set Y) := by
      rw [CFSG.layer.eq_sSup]
      apply sSup_le
      intro K hK k hk
      rw [mem_centralizer_iff]
      intro t ht
      have h1 : t ∈ centralizer (K : Set Y) := hT K ((CFSG.isComponent_iff_open K).mp hK) ht
      exact (mem_centralizer_iff.mp h1 k hk).symm
    intro t ht
    rw [mem_centralizer_iff]
    intro z hz
    exact (mem_centralizer_iff.mp (hlay hz) t ht).symm
  have key : (∀ o ∈ CFSG.pCore p Y, ∀ t ∈ T, o * t = t * o) → T ≤ CFSG.pCore p Y := by
    intro hc t ht
    have h2 : t ∈ centralizer (CFSG.pCore p Y : Set Y) := by
      rw [mem_centralizer_iff]
      intro o ho
      exact hc o ho t ht
    exact centralizer_layer_inf_centralizer_pCore_le h.core ⟨hTE ht, h2⟩
  have hOP : CFSG.pCore p Y ≤ P := by
    obtain ⟨S, hS⟩ := h.sylow
    rw [← hS]
    exact CFSG.pCore_isPGroup.le_sylow_of_normal S
  have hcomm : ∀ o ∈ CFSG.pCore p Y, ∀ t ∈ T,
      o * t * o⁻¹ * t⁻¹ ∈ CFSG.pCore p Y ⊓ zOf T := by
    intro o ho t ht
    refine ⟨?_, ?_⟩
    · have h1 : t * o⁻¹ * t⁻¹ ∈ CFSG.pCore p Y := hOn.conj_mem o⁻¹ (inv_mem ho) t
      have h2 : o * (t * o⁻¹ * t⁻¹) ∈ CFSG.pCore p Y := mul_mem ho h1
      simpa [mul_assoc] using h2
    · obtain ⟨t0, ht0, d0, hd0, rfl⟩ := h.exists_mul o (hOP ho)
      have h1 : d0 * t * d0⁻¹ = t := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (h.pdata.comm t ht d0 hd0).symm
      have h2 : t0 * d0 * t * (t0 * d0)⁻¹ * t⁻¹ = t0 * t * t0⁻¹ * t⁻¹ := by
        calc t0 * d0 * t * (t0 * d0)⁻¹ * t⁻¹
            = t0 * (d0 * t * d0⁻¹) * t0⁻¹ * t⁻¹ := by group
          _ = t0 * t * t0⁻¹ * t⁻¹ := by rw [h1]
      rw [h2]
      exact h.commutator_mem t0 ht0 t ht
  by_cases hbot : CFSG.pCore p Y ⊓ zOf T = ⊥
  ·
    apply key
    intro o ho t ht
    have h1 := hcomm o ho t ht
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : o * t * o⁻¹ = t := mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h2
  ·
    have hZO : zOf T ≤ CFSG.pCore p Y := by
      have hdvd : Nat.card (CFSG.pCore p Y ⊓ zOf T : Subgroup Y) ∣ Nat.card (zOf T) :=
        Subgroup.card_dvd_of_le inf_le_right
      rw [h.zOf_card] at hdvd
      rcases (Nat.dvd_prime h.prime).mp hdvd with h1 | h1
      · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hbot
      · have h2 : CFSG.pCore p Y ⊓ zOf T = zOf T :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h.zOf_card, h1])
        exact inf_eq_right.mp h2
    have hirr := h.torus.irred (T ⊓ CFSG.pCore p Y) inf_le_left (le_inf h.zOf_le hZO) (by
      intro f hf a ha
      exact ⟨h.torus.F_T f hf a ha.1, hOn.conj_mem a ha.2 f⟩)
    rcases hirr with hA | hA
    ·
      apply key
      intro o ho t ht
      obtain ⟨t0, ht0, d0, hd0, rfl⟩ := h.exists_mul o (hOP ho)
      have ht0Z : t0 ∈ zOf T := by
        apply h.torus.fpf t0 ht0
        intro f hf
        have h1 : f * t0 * f⁻¹ * t0⁻¹ ∈ T ⊓ CFSG.pCore p Y := by
          refine ⟨T.mul_mem (h.torus.F_T f hf t0 ht0) (T.inv_mem ht0), ?_⟩
          have h2 : f * (t0 * d0) * f⁻¹ * (t0 * d0)⁻¹ ∈ CFSG.pCore p Y :=
            mul_mem (hOn.conj_mem _ ho f) (inv_mem ho)
          have h3 : f * (t0 * d0) * f⁻¹ * (t0 * d0)⁻¹ = f * t0 * f⁻¹ * t0⁻¹ := by
            have hfd := h.F_D f hf d0 hd0
            calc f * (t0 * d0) * f⁻¹ * (t0 * d0)⁻¹
                = f * t0 * f⁻¹ * (f * d0 * f⁻¹) * d0⁻¹ * t0⁻¹ := by group
              _ = f * t0 * f⁻¹ * t0⁻¹ := by rw [hfd]; group
          rw [h3] at h2
          exact h2
        rw [hA] at h1
        exact h1
      have hc0 : t * t0 = t0 * t := mem_centralizer_iff.mp ht0Z.2 t ht
      have hct : t * d0 = d0 * t := h.pdata.comm t ht d0 hd0
      calc t0 * d0 * t = t0 * (d0 * t) := by rw [mul_assoc]
        _ = t0 * (t * d0) := by rw [hct]
        _ = (t0 * t) * d0 := by rw [mul_assoc]
        _ = (t * t0) * d0 := by rw [hc0]
        _ = t * (t0 * d0) := by rw [mul_assoc]
    · exact inf_eq_left.mp hA

end Case2Data3

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem mem_normalizer_of_pow_coprime {H : Subgroup Y} {y : Y} {n : ℕ}
    (hy : y ^ n = 1) {m : ℕ} (hm : Nat.Coprime m n) (hym : y ^ m ∈ normalizer (H : Set Y)) :
    y ∈ normalizer (H : Set Y) := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hm hn
    have h1 : y = (y ^ m) ^ k := by
      rw [← pow_mul, pow_eq_pow_mod (m * k) hy, hk, pow_one]
    rw [h1]
    exact pow_mem hym k
  · rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · have hm1 : m = 1 := by simpa using hm
      subst hm1
      simpa using hym
    · have hy1 : y = 1 := by simpa using hy
      subst hy1
      exact one_mem _

theorem exists_mem_P_inf (h : Case2Data3 p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    ∃ t ∈ P ⊓ L, orderOf t = p ∧ t ∉ centralizer (L : Set Y) := by
  obtain ⟨S, hS⟩ := h.sylow
  subst hS
  have hp2 : p ≠ 2 := by have := h.three; omega
  exact exists_mem_sylow_inf_component h.prime hp2 h.core S hL

theorem commutator_P (h : Case2Data3 p P T D F x) {a b : Y} (ha : a ∈ P) (hb : b ∈ P) :
    a * b * a⁻¹ * b⁻¹ ∈ zOf T := by
  obtain ⟨t, ht, d, hd, rfl⟩ := h.exists_mul a ha
  obtain ⟨t', ht', d', hd', rfl⟩ := h.exists_mul b hb
  have h1 : Commute d t' := (h.pdata.comm t' ht' d hd).symm
  have h2 : Commute d' t := (h.pdata.comm t ht d' hd').symm
  have h3 : d * d' = d' * d := D_comm h d hd d' hd'
  have e1 : t * d * (t' * d') = t * t' * (d * d') := h1.mul_mul_mul_comm t d'
  have e2 : t' * d' * (t * d) = t' * t * (d' * d) := h2.mul_mul_mul_comm t' d
  have hc := h.commutator_mem t ht t' ht'
  have e3 : t * d * (t' * d') = (t * t' * t⁻¹ * t'⁻¹) * (t' * d' * (t * d)) := by
    rw [e1, e2, ← h3]; group
  have e4 : t * d * (t' * d') * (t * d)⁻¹ * (t' * d')⁻¹ = t * t' * t⁻¹ * t'⁻¹ := by
    rw [e3]; group
  rw [e4]; exact hc

theorem P_le_normalizer (h : Case2Data3 p P T D F x) {L : Subgroup Y} (hL : IsComponentOf L ⊤) :
    P ≤ normalizer (L : Set Y) := by
  classical
  intro y hy
  by_contra hyL
  have hp3 : p = 3 := h.three
  obtain ⟨k, hk⟩ := h.exists_pow_eq_one y hy
  obtain ⟨t, htPL, -, htc⟩ := h.exists_mem_P_inf hL
  obtain ⟨htP, htL⟩ := Subgroup.mem_inf.mp htPL
  set f : ℕ → Subgroup Y := fun i => L.map (MulAut.conj (y ^ i)).toMonoidHom with hf
  have hfK : ∀ i, IsComponentOf (f i) ⊤ := fun i =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (y ^ i)) L).mpr hL
  have key : ∀ i j : ℕ, i < j → j < 3 → f i ≠ f j := by
    intro i j hij hj hfij
    apply hyL
    refine mem_normalizer_of_pow_coprime hk (m := j - i) ?_ ?_
    · have hcop : Nat.Coprime (j - i) p :=
        (Nat.coprime_of_lt_prime (by omega) (by omega) h.prime).symm
      exact Nat.Coprime.pow_right k hcop
    · rw [mem_normalizer_iff_map_conj_eq]
      have h1 : f j = (f (j - i)).map (MulAut.conj (y ^ i)).toMonoidHom := by
        simp only [hf]
        rw [← CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, ← pow_add,
          Nat.add_sub_cancel' hij.le]
      rw [h1] at hfij
      exact (map_injective (MulAut.conj (y ^ i)).injective hfij).symm
  have hcomm : ∀ i j : ℕ, i < j → j < 3 → ∀ a ∈ f i, ∀ b ∈ f j, a * b = b * a := by
    intro i j hij hj a ha b hb
    have hLL : ⁅f i, f j⁆ = ⊥ :=
      CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hfK i) (hfK j)
        (key i j hij hj)
    exact (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hLL ha) b hb).symm
  have hmem : ∀ i : ℕ, y ^ i * t * (y ^ i)⁻¹ ∈ f i := fun i => ⟨t, htL, rfl⟩
  have hf0 : f 0 = L := by
    have h1 : (MulAut.conj (y ^ 0)).toMonoidHom = MonoidHom.id Y := by
      ext g
      simp
    simp only [hf, h1, Subgroup.map_id]
  set b : Y := y ^ 1 * t * (y ^ 1)⁻¹ with hb
  set c : Y := y ^ 2 * t * (y ^ 2)⁻¹ with hc
  have hbf : b ∈ f 1 := hmem 1
  have hcf : c ∈ f 2 := hmem 2
  have hu := h.commutator_P hy htP
  have hcen : (y * t * y⁻¹ * t⁻¹) * y = y * (y * t * y⁻¹ * t⁻¹) := h.zOf_central _ hu y hy
  have hconj : y * (y * t * y⁻¹ * t⁻¹) * y⁻¹ = y * t * y⁻¹ * t⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hcen.symm
  have heq : c * b⁻¹ = b * t⁻¹ := by
    calc c * b⁻¹ = y * (y * t * y⁻¹ * t⁻¹) * y⁻¹ := by simp only [hb, hc, pow_one, pow_two]; group
      _ = y * t * y⁻¹ * t⁻¹ := hconj
      _ = b * t⁻¹ := by simp only [hb, pow_one]
  have ht_eq : t = b * c⁻¹ * b := by
    have h1 : t⁻¹ = b⁻¹ * (c * b⁻¹) := by rw [heq]; group
    calc t = (t⁻¹)⁻¹ := (inv_inv t).symm
      _ = (b⁻¹ * (c * b⁻¹))⁻¹ := by rw [h1]
      _ = b * c⁻¹ * b := by group
  apply htc
  rw [mem_centralizer_iff]
  intro l hl
  have hl0 : l ∈ f 0 := hf0 ▸ hl
  have hlb : Commute l b := hcomm 0 1 (by norm_num) (by norm_num) l hl0 b hbf
  have hlc : Commute l c := hcomm 0 2 (by norm_num) (by norm_num) l hl0 c hcf
  rw [ht_eq]
  exact ((hlb.mul_right hlc.inv_right).mul_right hlb).eq

end Case2Data3

private lemma pow_mul_mem_of_conj_mem {Y : Type*} [Group Y] {N : Subgroup Y} {a : Y}
    (ha : ∀ n ∈ N, a⁻¹ * n * a ∈ N) (n : Y) (hn : n ∈ N) (m : ℕ) :
    ∃ n' ∈ N, (a * n) ^ m = a ^ m * n' := by
  induction m with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨n', hn', h⟩ := ih
    refine ⟨a⁻¹ * n' * a * n, N.mul_mem (ha n' hn') hn, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

private lemma pow_mul_mem_of_pow_eq_one {Y : Type*} [Group Y] {N : Subgroup Y} {a : Y}
    (ha : ∀ n ∈ N, a⁻¹ * n * a ∈ N) {m : ℕ} (hm : a ^ m = 1) (n : Y) (hn : n ∈ N) :
    (a * n) ^ m ∈ N := by
  obtain ⟨n', hn', h⟩ := pow_mul_mem_of_conj_mem ha n hn m
  rw [h, hm, one_mul]
  exact hn'

private lemma not_isPGroup_quotient_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hc : commutator G = ⊤)
    [hs : IsSimpleGroup (G ⧸ Subgroup.center G)] :
    ¬ IsPGroup p (G ⧸ Subgroup.center G) := by
  intro hpg
  have hbot : (⊥ : Subgroup (G ⧸ Subgroup.center G)) < Subgroup.center (G ⧸ Subgroup.center G) :=
    hpg.bot_lt_center
  have htop : Subgroup.center (G ⧸ Subgroup.center G) = ⊤ :=
    (hs.eq_bot_or_eq_top_of_normal (Subgroup.center (G ⧸ Subgroup.center G))).resolve_left hbot.ne'
  have hcomm_bot : commutator (G ⧸ Subgroup.center G) = ⊥ :=
    (commutator_eq_bot_iff_center_eq_top _).mpr htop
  have hsurj : Function.Surjective
      (QuotientGroup.mk' (Subgroup.center G) : G →* G ⧸ Subgroup.center G) :=
    QuotientGroup.mk'_surjective _
  have key : (commutator G).map (QuotientGroup.mk' (Subgroup.center G)) =
      commutator (G ⧸ Subgroup.center G) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj, _root_.commutator_def]
  have hcomm_top : commutator (G ⧸ Subgroup.center G) = ⊤ := by
    rw [← key, hc]
    exact Subgroup.map_top_of_surjective _ hsurj
  have h1 : (⊤ : Subgroup (G ⧸ Subgroup.center G)) = ⊥ := hcomm_top.symm.trans hcomm_bot
  obtain ⟨z, hz⟩ := exists_ne (1 : G ⧸ Subgroup.center G)
  have hz' : z ∈ (⊥ : Subgroup (G ⧸ Subgroup.center G)) := by
    rw [← h1]
    exact Subgroup.mem_top z
  exact hz (Subgroup.mem_bot.mp hz')

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

theorem not_le_centralizer_x (h : Case2Data3 p P T D F x) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    ¬ L ≤ centralizer ({x} : Set Y) := by
  intro hLW
  obtain ⟨N, hser⟩ := h.series
  haveI : Fact p.Prime := h.fact
  have h5 : p = 3 := h.three
  obtain ⟨S, hS⟩ := h.sylow
  obtain ⟨t, htmem, hto, htc⟩ :=
    exists_mem_sylow_inf_component h.prime (by omega) h.core S hL
  rw [hS] at htmem
  obtain ⟨htP, htL⟩ := Subgroup.mem_inf.mp htmem
  have ht_pow : t ^ p = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hto] at this
  have hPp : ∀ a ∈ P, ∃ k : ℕ, a ^ p ^ k = 1 := by
    intro a ha
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨a, by rw [hS]; exact ha⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hPW : P ≤ centralizer ({x} : Set Y) := hser.P_le
  have hPN : P ≤ Subgroup.normalizer N := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hser.N_norm g (hPW hg) n hn
    · intro hn
      have := hser.N_norm g⁻¹ ((centralizer ({x} : Set Y)).inv_mem (hPW hg)) _ hn
      rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this
  have hdecomp : ∀ q ∈ P ⊔ N, ∃ a ∈ P, ∃ n ∈ N, q = a * n := by
    intro q hq
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P N hPN, Set.mem_mul] at hq
    obtain ⟨a, ha, n, hn, hq'⟩ := hq
    exact ⟨a, ha, n, hn, hq'.symm⟩
  have hconj : ∀ a ∈ P, ∀ n ∈ N, a⁻¹ * n * a ∈ N := by
    intro a ha n hn
    have := hser.N_norm a⁻¹ ((centralizer ({x} : Set Y)).inv_mem (hPW ha)) n hn
    rwa [inv_inv] at this
  have hPNpow : ∀ q ∈ P ⊔ N, ∃ k : ℕ, q ^ p ^ k ∈ N := by
    intro q hq
    obtain ⟨a, ha, n, hn, rfl⟩ := hdecomp q hq
    obtain ⟨k, hk⟩ := hPp a ha
    exact ⟨k, pow_mul_mem_of_pow_eq_one (hconj a ha) hk n hn⟩
  obtain ⟨hcomm, hsimp⟩ := hL.2.2
  haveI := hsimp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : L →* L ⧸ Subgroup.center L, ρ = QuotientGroup.mk' (Subgroup.center L) :=
    ⟨_, rfl⟩
  have hρsurj : Function.Surjective ρ := by
    rw [hρ]
    exact QuotientGroup.mk'_surjective _
  have hker : ∀ a : L, ρ a = 1 ↔ a ∈ Subgroup.center L := by
    intro a
    rw [hρ]
    exact QuotientGroup.eq_one_iff a
  have hK₁ : (N.subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hser.N_norm (g : Y) (hLW g.2) (n : Y) hn
    simpa using this
  have hK₂ : ((P ⊔ N).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hser.PN_norm (g : Y) (hLW g.2) (n : Y) hn
    simpa using this
  obtain ⟨t', ht'⟩ : ∃ t' : L, (t' : Y) = t := ⟨⟨t, htL⟩, rfl⟩
  have ht'_pow : t' ^ p = 1 := by
    apply Subtype.ext
    simp [ht', ht_pow]
  have hρt_pow : ρ t' ^ p = 1 := by
    rw [← map_pow, ht'_pow, map_one]
  have hρt : ρ t' ≠ 1 := by
    intro h1
    apply htc
    have hcen := Subgroup.mem_center_iff.mp ((hker t').mp h1)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := congrArg Subtype.val (hcen ⟨l, hl⟩)
    rw [← ht']
    simpa using this
  have htPN : t ∈ P ⊔ N := (le_sup_left : P ≤ P ⊔ N) htP
  haveI hK₁map : ((N.subgroupOf L).map ρ).Normal := hK₁.map ρ hρsurj
  rcases hsimp.eq_bot_or_eq_top_of_normal ((N.subgroupOf L).map ρ) with hA₁ | hA₁
  ·
    haveI hK₂map : (((P ⊔ N).subgroupOf L).map ρ).Normal := hK₂.map ρ hρsurj
    have hB : ((P ⊔ N).subgroupOf L).map ρ = ⊤ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (((P ⊔ N).subgroupOf L).map ρ) with hB | hB
      · exfalso
        have hmem : ρ t' ∈ ((P ⊔ N).subgroupOf L).map ρ :=
          Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr (by rw [ht']; exact htPN))
        rw [hB, Subgroup.mem_bot] at hmem
        exact hρt hmem
      · exact hB
    have hPG : IsPGroup p (L ⧸ Subgroup.center L) := by
      intro q
      have hq : q ∈ ((P ⊔ N).subgroupOf L).map ρ := by
        rw [hB]
        exact Subgroup.mem_top q
      obtain ⟨ℓ, hℓ, rfl⟩ := Subgroup.mem_map.mp hq
      obtain ⟨k, hk⟩ := hPNpow (ℓ : Y) (Subgroup.mem_subgroupOf.mp hℓ)
      refine ⟨k, ?_⟩
      have hmem : ℓ ^ p ^ k ∈ N.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hk
      have h1 : ρ (ℓ ^ p ^ k) ∈ (N.subgroupOf L).map ρ := Subgroup.mem_map_of_mem ρ hmem
      rw [hA₁, Subgroup.mem_bot] at h1
      rw [← map_pow]
      exact h1
    exact not_isPGroup_quotient_center hcomm hPG
  ·
    have hmem : ρ t' ∈ (N.subgroupOf L).map ρ := by
      rw [hA₁]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hρn⟩ := Subgroup.mem_map.mp hmem
    have hnN : (n : Y) ∈ N := Subgroup.mem_subgroupOf.mp hn
    have hkn : n ^ orderOf (n : Y) = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    have hρk : ρ t' ^ orderOf (n : Y) = 1 := by
      rw [← hρn, ← map_pow, hkn, map_one]
    have hgcd : orderOf (ρ t') ∣ Nat.gcd p (orderOf (n : Y)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hρt_pow) (orderOf_dvd_of_pow_eq_one hρk)
    have hcop : Nat.gcd p (orderOf (n : Y)) = 1 := hser.N_cop (n : Y) hnN
    rw [hcop] at hgcd
    exact hρt (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd))

end Case2Data3

namespace Case2Data3

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P T D F : Subgroup Y} {x : Y}

private theorem T_comm_of_commute (h : Case2Data3 p P T D F x) {u : Y} (hu : u ∈ T)
    (hnc : u ∉ zOf T) {a b : Y} (ha : a ∈ T) (hb : b ∈ T)
    (hau : a * u = u * a) (hbu : b * u = u * b) : a * b = b * a := by
  haveI := h.fact
  have hZcard : Nat.card (zOf T) = p :=
    card_inf_centralizer_of_nonabelian_card_p_cube h.pdata.T_card h.pdata.T_nonab
  set C : Subgroup Y := T ⊓ centralizer ({u} : Set Y) with hC
  have hCT : C ≤ T := inf_le_left
  have hZC : zOf T ≤ C :=
    inf_le_inf_left T (centralizer_le (Set.singleton_subset_iff.mpr hu))
  have hdvd1 : Nat.card C ∣ p ^ 3 := h.pdata.T_card ▸ Subgroup.card_dvd_of_le hCT
  have hdvd2 : p ∣ Nat.card C := hZcard ▸ Subgroup.card_dvd_of_le hZC
  obtain ⟨i, hi, hCi⟩ := (Nat.dvd_prime_pow h.prime).mp hdvd1
  have hmemC : u ∈ C := ⟨hu, mem_centralizer_iff.mpr (by simp)⟩
  have hi2 : i = 2 := by
    interval_cases i
    · exfalso
      rw [pow_zero] at hCi
      rw [hCi] at hdvd2
      have := Nat.le_of_dvd one_pos hdvd2
      have := h.three
      omega
    · exfalso
      apply hnc
      have hZeq : zOf T = C := Subgroup.eq_of_le_of_card_ge hZC (by rw [hCi, hZcard, pow_one])
      rw [hZeq]
      exact hmemC
    · rfl
    · exfalso
      apply hnc
      have hCeq : C = T :=
        Subgroup.eq_of_le_of_card_ge hCT (by rw [hCi, h.pdata.T_card])
      refine ⟨hu, mem_centralizer_iff.mpr fun g hg => ?_⟩
      have hgC : g ∈ C := hCeq ▸ hg
      exact (mem_centralizer_iff.mp hgC.2 u (Set.mem_singleton u)).symm
  have hcomm : IsMulCommutative C := by
    rw [hi2] at hCi
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hCi
  have haC : a ∈ C := ⟨ha, mem_centralizer_iff.mpr (by simpa using hau.symm)⟩
  have hbC : b ∈ C := ⟨hb, mem_centralizer_iff.mpr (by simpa using hbu.symm)⟩
  exact setLike_mul_comm haC hbC

private theorem comm_iff (h : Case2Data3 p P T D F x) {t t' : Y} (ht : t ∈ T) (ht' : t' ∈ T)
    {d d' : Y} (hd : d ∈ D) (hd' : d' ∈ D) :
    (t * d) * (t' * d') = (t' * d') * (t * d) ↔ t * t' = t' * t := by
  have e1 : d * t' = t' * d := (h.pdata.comm t' ht' d hd).symm
  have e2 : d' * t = t * d' := (h.pdata.comm t ht d' hd').symm
  haveI := h.pdata.D_cyc
  have e3 : d * d' = d' * d := setLike_mul_comm hd hd'
  have l : (t * d) * (t' * d') = (t * t') * (d * d') := by
    calc (t * d) * (t' * d') = t * (d * t') * d' := by simp only [mul_assoc]
      _ = t * (t' * d) * d' := by rw [e1]
      _ = (t * t') * (d * d') := by simp only [mul_assoc]
  have r : (t' * d') * (t * d) = (t' * t) * (d * d') := by
    calc (t' * d') * (t * d) = t' * (d' * t) * d := by simp only [mul_assoc]
      _ = t' * (t * d') * d := by rw [e2]
      _ = (t' * t) * (d' * d) := by simp only [mul_assoc]
      _ = (t' * t) * (d * d') := by rw [e3]
  rw [l, r]
  exact mul_left_inj _

open CFSG.ABGLocalTools in
private theorem exists_noncomm_inf (h : Case2Data3 p P T D F x) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hc : center L ≠ ⊥) :
    ∃ a ∈ P ⊓ L, ∃ b ∈ P ⊓ L, a * b ≠ b * a := by
  by_contra hcon0
  have hcon : ∀ a ∈ P ⊓ L, ∀ b ∈ P ⊓ L, a * b = b * a := fun a ha b hb => by
    by_contra hne
    exact hcon0 ⟨a, ha, b, hb, hne⟩
  apply hc
  haveI := h.fact
  have hN : P ≤ normalizer (L : Set Y) := h.P_le_normalizer hL
  have hPsyl : IsSylowOf p P ⊤ := by
    obtain ⟨S, hS⟩ := h.sylow
    rw [isSylowOf_iff]
    refine ⟨le_top, hS ▸ S.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right, ← hS]
    exact S.not_dvd_index
  have hPL : IsSylowOf p (P ⊓ L) L :=
    (hPsyl.of_le (le_sup_left : P ≤ P ⊔ L) le_top).inf_of_le_normalizer le_sup_right
      (sup_le hN le_normalizer)
  obtain ⟨Q, hQ⟩ := hPL.exists_sylow_eq_subgroupOf
  have hQab : IsMulCommutative (Q : Subgroup L) :=
    IsMulCommutative.of_comm fun a b => by
      have ha : (a : Y) ∈ P ⊓ L :=
        Subgroup.mem_subgroupOf.mp ((SetLike.ext_iff.mp hQ a.1).mp a.2)
      have hb : (b : Y) ∈ P ⊓ L :=
        Subgroup.mem_subgroupOf.mp ((SetLike.ext_iff.mp hQ b.1).mp b.2)
      exact Subtype.ext (Subtype.ext (hcon _ ha _ hb))
  have key := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup Q hQab (Z := center L) le_rfl
    (isPGroup_center_of_isComponentOf h.prime h.core hL)
  rwa [hL.2.2.1, inf_top_eq] at key

theorem eq_of_center_ne_bot (h : Case2Data3 p P T D F x) {L L' : Subgroup Y}
    (hL : IsComponentOf L ⊤) (hL' : IsComponentOf L' ⊤) (hc : center L ≠ ⊥) (hc' : center L' ≠ ⊥) :
    L = L' := by
  by_contra hne
  obtain ⟨a₁, ha₁, a₂, ha₂, ha⟩ := h.exists_noncomm_inf hL hc
  obtain ⟨b₁, hb₁, b₂, hb₂, hb⟩ := h.exists_noncomm_inf hL' hc'
  have hLL : ⁅L, L'⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne L L' hL hL' hne
  have hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hLL ha) b hb).symm
  obtain ⟨t₁, ht₁, d₁, hd₁, rfl⟩ := h.exists_mul a₁ ha₁.1
  obtain ⟨t₂, ht₂, d₂, hd₂, rfl⟩ := h.exists_mul a₂ ha₂.1
  obtain ⟨u₁, hu₁, e₁, he₁, rfl⟩ := h.exists_mul b₁ hb₁.1
  obtain ⟨u₂, hu₂, e₂, he₂, rfl⟩ := h.exists_mul b₂ hb₂.1
  have hat : t₁ * t₂ ≠ t₂ * t₁ := fun e => ha ((h.comm_iff ht₁ ht₂ hd₁ hd₂).mpr e)
  have hbt : u₁ * u₂ ≠ u₂ * u₁ := fun e => hb ((h.comm_iff hu₁ hu₂ he₁ he₂).mpr e)
  have hcross : ∀ {t d u e : Y}, t ∈ T → d ∈ D → u ∈ T → e ∈ D →
      t * d ∈ L → u * e ∈ L' → t * u = u * t := fun ht hd hu he hL hL' =>
    (h.comm_iff ht hu hd he).mp (hcomm _ hL _ hL')
  have hnc : u₁ ∉ zOf T := fun hz =>
    hbt (mem_centralizer_iff.mp hz.2 u₂ hu₂).symm
  exact hat (h.T_comm_of_commute hu₁ hnc ht₁ ht₂
    (hcross ht₁ hd₁ hu₁ he₁ ha₁.2 hb₁.2)
    (hcross ht₂ hd₂ hu₁ he₁ ha₂.2 hb₁.2))

end Case2Data3

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3U3RemarkAux
