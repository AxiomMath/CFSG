module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710Tools
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7ToolsB
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Case1
public import CFSG.LocalAnalysis.GLTheoremB.CentralizerLift

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem le_glaPPrimeCoreOf_of_inf {p : ℕ} (hp : p.Prime) {A I : Subgroup G}
    (hAI : A ≤ Subgroup.normalizer (GLAPPrimeCoreOf p I : Set G)) :
    A ⊓ GLAPPrimeCoreOf p I ≤ GLAPPrimeCoreOf p A := by
  set O := GLAPPrimeCoreOf p I with hO
  set N0 : Subgroup ↥A := O.subgroupOf A with hN0
  have hnorm : N0.Normal := by
    refine ⟨fun n hn h' => ?_⟩
    show ((h' * n * h'⁻¹ : ↥A) : G) ∈ O
    have := (Subgroup.mem_normalizer_iff.1 (hAI h'.2) (n : G)).1 hn
    simpa using this
  have hdvd : Nat.card N0 ∣ Nat.card O := by
    have h1 : N0.map A.subtype = A ⊓ O := by
      rw [hN0, ← Subgroup.inf_subgroupOf_right O A]
      rw [Subgroup.map_subgroupOf_eq_of_le (inf_le_right : O ⊓ A ≤ A)]
      exact inf_comm _ _
    have h2 : Nat.card (N0.map A.subtype) = Nat.card N0 :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [← h2, h1]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hcop : Nat.Coprime p (Nat.card N0) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd =>
      not_dvd_card_glaPPrimeCoreOf hp I (hd.trans hdvd)
  have hle : N0 ≤ GLAPPrimeCore p ↥A := le_sSup ⟨hnorm, hcop⟩
  intro x hx
  exact ⟨⟨x, hx.1⟩, hle ((Subgroup.mem_subgroupOf).2 hx.2), rfl⟩

private def threePart (K : Subgroup G) : Subgroup ↥K :=
  Subgroup.closure {k : ↥K | ∃ n : ℕ, k ^ (3 ^ n) = 1}

omit [Finite G] in
private theorem threePart_normal (K : Subgroup G) : (threePart K).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨m, hm⟩ := hx
    refine Subgroup.subset_closure ⟨m, ?_⟩
    rw [conj_pow, hm]
    simp
  | one => simp
  | mul x y _ _ hx hy =>
    have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ hx

theorem le_sup_primeCore_of_forall {K H : Subgroup G}
    (hKl : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K))
    (hH : ∀ k ∈ K, (∃ n : ℕ, k ^ (3 ^ n) = 1) → k ∈ H) :
    K ≤ H ⊔ GLAPPrimeCoreOf 3 K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥K := GLAPPrimeCore 3 ↥K with hN
  have hsimple : IsSimpleGroup (↥K ⧸ N) := (isSimpleGroup_of_isLThreeFour hKl).1
  have hcardQ : Nat.card (↥K ⧸ N) = 20160 := card_eq_of_isLThreeFour hKl
  have hN3 : ¬ 3 ∣ Nat.card N := by
    have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  have hdvdK : 3 ∣ Nat.card ↥K := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h1, hcardQ]
    exact Dvd.dvd.mul_right (by norm_num) _
  have htop : threePart K ⊔ N = ⊤ := by
    have hn : ((threePart K).map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map (threePart_normal K) _ (QuotientGroup.mk'_surjective N)
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple
      ((threePart K).map (QuotientGroup.mk' N)) hn with hbot | htopQ
    · exfalso
      have hle : threePart K ≤ N := by
        intro x hx
        have : QuotientGroup.mk' N x ∈ (threePart K).map (QuotientGroup.mk' N) := ⟨x, hx, rfl⟩
        rw [hbot] at this
        exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 this)
      obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 hdvdK
      have hk3 : k ^ (3 ^ 1) = 1 := by rw [pow_one, ← hk]; exact pow_orderOf_eq_one k
      have hkN : k ∈ N := hle (Subgroup.subset_closure ⟨1, hk3⟩)
      have hdvd := Subgroup.orderOf_dvd_natCard N hkN
      rw [hk] at hdvd
      exact hN3 hdvd
    · have := Subgroup.comap_map_eq (QuotientGroup.mk' N) (threePart K)
      rw [htopQ, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
  have hle : threePart K ≤ H.subgroupOf K := by
    rw [threePart, Subgroup.closure_le]
    intro x hx
    obtain ⟨m, hm⟩ := hx
    exact hH x x.2 ⟨m, by
      have := congrArg Subtype.val hm
      simpa using this⟩
  intro k hk
  have hkW : (⟨k, hk⟩ : ↥K) ∈ H.subgroupOf K ⊔ N :=
    (sup_le_sup_right hle N) (htop ▸ Subgroup.mem_top _)
  have : k ∈ (H.subgroupOf K ⊔ N).map K.subtype := ⟨⟨k, hk⟩, hkW, rfl⟩
  rw [Subgroup.map_sup] at this
  refine (sup_le_sup ?_ le_rfl : _ ≤ H ⊔ GLAPPrimeCoreOf 3 K) this
  rintro _ ⟨y, hy, rfl⟩
  exact hy

omit [Finite G] in
private theorem mem_preimBarX_of_mem {p : ℕ} {X K : Subgroup G} {z : G}
    (hz : z ∈ GLAPPrimeCoreOf p X) : z ∈ preimBarX p X K := by
  obtain ⟨z', hz', rfl⟩ := hz
  refine ⟨z', ?_, rfl⟩
  refine Subgroup.mem_comap.2 ?_
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) z' = 1 := (QuotientGroup.eq_one_iff z').2 hz'
  rw [h1]
  exact Subgroup.one_mem _

theorem covers3_of_cover_I {B I K N' : Subgroup G} {x₀ : G} (hBel : IsElemAbelian 3 B)
    (hx₀ : x₀ ∈ B) (hx₀1 : x₀ ≠ 1) (hBN' : B ≤ N') (hBI : B ≤ Subgroup.normalizer (I : Set G))
    (hKc : GLAPComponent 3 (Subgroup.centralizer ({x₀} : Set G)) K)
    (hKl : IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K)) (hKI : K ≤ I)
    (hIK : I ≤ K ⊔ GLAPPrimeCoreOf 3 I) (hcov : I ≤ (N' ⊓ I) ⊔ GLAPPrimeCoreOf 3 I) :
    Covers3 N' K := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp3⟩
  set O := GLAPPrimeCoreOf 3 I with hO
  set C := Subgroup.centralizer ({x₀} : Set G) with hC
  set J := N' ⊓ I with hJ
  set D := I ⊓ C with hD
  set E := J ⊓ C with hE
  set Z := D ⊓ O with hZ
  have hOn : I ≤ Subgroup.normalizer (O : Set G) := le_normalizer_glaPPrimeCoreOf 3 I
  have hO3 : ¬ 3 ∣ Nat.card O := not_dvd_card_glaPPrimeCoreOf hp3 I
  have hKC : K ≤ C := hKc.1
  have hKD : K ≤ D := le_inf hKI hKC
  have hDC : D ≤ C := inf_le_right
  have hDI : D ≤ I := inf_le_left
  have hJI : J ≤ I := inf_le_right
  have hJN : J ≤ N' := inf_le_left
  have hEJ : E ≤ J := inf_le_left
  have hED : E ≤ D := le_inf (hEJ.trans hJI) inf_le_right
  have hZD : Z ≤ D := inf_le_left
  have hZ3 : ¬ 3 ∣ Nat.card Z := fun h => hO3 (h.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hZn : D ≤ Subgroup.normalizer (Z : Set G) := fun g hg =>
    mem_normalizer_inf (Subgroup.le_normalizer hg) (hOn (hDI hg))
  have hmul : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (O : Set G) → ∀ x ∈ A ⊔ O,
      ∃ a ∈ A, ∃ o ∈ O, x = a * o := by
    intro A hA x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A O hA] at hx
    obtain ⟨a, ha, o, ho, rfl⟩ := hx
    exact ⟨a, ha, o, ho, rfl⟩
  have hdec : ∀ d ∈ D, ∃ k ∈ K, ∃ z ∈ Z, d = k * z := by
    intro d hd
    obtain ⟨k, hk, o, ho, rfl⟩ := hmul K (hKI.trans hOn) d (hIK (hDI hd))
    refine ⟨k, hk, o, ⟨?_, ho⟩, rfl⟩
    have : o = k⁻¹ * (k * o) := by simp
    rw [this]
    exact D.mul_mem (D.inv_mem (hKD hk)) hd
  have hKnorm : D ≤ Subgroup.normalizer (K : Set G) := by
    have hKD' : GLAPComponent 3 D K := glaPComponent_of_le hp3 hKc hKD hDC
    have hn := glaPComponent_normal_preimBarX hKD'
    have hKP : K ≤ preimBarX 3 D K := le_preimBarX 3 hKD
    have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hKP).1 hn
    refine le_trans (fun d hd => ?_) hle
    obtain ⟨k, hk, z, hz, rfl⟩ := hdec d hd
    refine (preimBarX 3 D K).mul_mem (le_preimBarX 3 hKD hk) (mem_preimBarX_of_mem ?_)
    exact le_glaPPrimeCoreOf_of_inf hp3 (fun g hg => hOn (hDI hg)) hz
  have hK3 : ∀ y ∈ D, (∃ n : ℕ, y ^ (3 ^ n) = 1) → y ∈ K := by
    intro y hy ⟨n, hn⟩
    have hM : D ≤ Z ⊔ K := by
      intro d hd
      obtain ⟨k, hk, z, hz, rfl⟩ := hdec d hd
      exact (Z ⊔ K).mul_mem ((le_sup_right : K ≤ Z ⊔ K) hk) ((le_sup_left : Z ≤ Z ⊔ K) hz)
    obtain ⟨z, hz, r, hr, -, rfl⟩ := sylow_lift (p := 3) hKD hZD hZn hZ3 hM hy hn
    exact (Subgroup.mem_normalizer_iff.1 (hKnorm (hZD hz)) r).1 hr
  have hx₀3 : x₀ ^ 3 = 1 := hBel.2 x₀ hx₀
  have hpg : IsPGroup 3 (Subgroup.zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx₀3 hx₀1, pow_one])
  have hx₀I : x₀ ∈ Subgroup.normalizer (I : Set G) := hBI hx₀
  have hx₀O : x₀ ∈ Subgroup.normalizer (O : Set G) :=
    le_normalizer_glaPPrimeCoreOf_of_le' (p := 3) hBI hx₀
  have hx₀J : ∀ j ∈ J, x₀ * j * x₀⁻¹ ∈ J := fun j hj =>
    ⟨(N').mul_mem ((N').mul_mem (hBN' hx₀) hj.1) ((N').inv_mem (hBN' hx₀)),
      (Subgroup.mem_normalizer_iff.1 hx₀I j).1 hj.2⟩
  have hDEZ : ∀ d ∈ D, ∃ e ∈ E, ∃ z ∈ Z, d = e * z := by
    intro d hd
    obtain ⟨j, hj, o, ho, rfl⟩ := hmul J (hJI.trans hOn) d (hcov (hDI hd))
    have hcomm : x₀ * j * x₀⁻¹ * j⁻¹ ∈ J ⊓ O := by
      refine ⟨J.mul_mem (hx₀J j hj) (J.inv_mem hj), ?_⟩
      obtain ⟨k, hk, o', ho', rfl⟩ := hmul K (hKI.trans hOn) j (hIK (hJI hj))
      have hxk : x₀ * k = k * x₀ := by
        have := hKC hk
        rw [hC, Subgroup.mem_centralizer_singleton_iff] at this
        exact this.symm
      have e : x₀ * (k * o') * x₀⁻¹ * (k * o')⁻¹ = k * (x₀ * o' * x₀⁻¹ * o'⁻¹) * k⁻¹ := by
        have h1 : x₀ * (k * o') * x₀⁻¹ = k * (x₀ * o' * x₀⁻¹) := by
          calc x₀ * (k * o') * x₀⁻¹ = (x₀ * k) * o' * x₀⁻¹ := by group
            _ = k * (x₀ * o' * x₀⁻¹) := by rw [hxk]; group
        rw [h1]; group
      rw [e]
      have h2 : x₀ * o' * x₀⁻¹ * o'⁻¹ ∈ O :=
        O.mul_mem ((Subgroup.mem_normalizer_iff.1 hx₀O o').1 ho') (O.inv_mem ho')
      have h3 := (Subgroup.mem_normalizer_iff.1 (hOn (hKI hk)) _).1 h2
      exact h3
    have hx₀Jn : x₀ ∈ Subgroup.normalizer (J : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨hx₀J y, fun h => ⟨?_, (Subgroup.mem_normalizer_iff.1 hx₀I y).2 h.2⟩⟩
      have := N'.mul_mem (N'.mul_mem (N'.inv_mem (hBN' hx₀)) h.1) (hBN' hx₀)
      simpa [mul_assoc] using this
    obtain ⟨v, hv, hvC⟩ := exists_mul_mem_centralizer (p := 3) (d := x₀) (x := j) (V := J ⊓ O) hpg
      (fun h => hO3 (h.trans (Subgroup.card_dvd_of_le inf_le_right)))
      (mem_normalizer_inf hx₀Jn hx₀O)
      (mem_normalizer_inf (Subgroup.le_normalizer hj) (hOn (hJI hj))) hcomm
    have heJ : j * v ∈ J := J.mul_mem hj hv.1
    have heE : j * v ∈ E := ⟨heJ, hvC⟩
    refine ⟨j * v, heE, v⁻¹ * o, ⟨?_, O.mul_mem (O.inv_mem hv.2) ho⟩, by group⟩
    have : v⁻¹ * o = (j * v)⁻¹ * (j * o) := by group
    rw [this]
    exact D.mul_mem (D.inv_mem (hED heE)) hd
  have hfin := le_sup_primeCore_of_forall (K := K)
    (H := (N' ⊓ K) ⊔ GLAPPrimeCoreOf 3 K) hKl
  rw [sup_eq_left.2 (le_sup_right : GLAPPrimeCoreOf 3 K ≤ (N' ⊓ K) ⊔ GLAPPrimeCoreOf 3 K)] at hfin
  refine hfin fun k hk ⟨n, hn⟩ => ?_
  have hkD : k ∈ D := hKD hk
  obtain ⟨z, hz, r, hr, ⟨m, hm⟩, hkzr⟩ := sylow_lift (p := 3) hED hZD hZn hZ3
    (fun d hd => by
      obtain ⟨e, he, z, hz, rfl⟩ := hDEZ d hd
      exact (Z ⊔ E).mul_mem ((le_sup_right : E ≤ Z ⊔ E) he) ((le_sup_left : Z ≤ Z ⊔ E) hz))
    hkD hn
  have hrK : r ∈ K := hK3 r (hED hr) ⟨m, hm⟩
  have hrN : r ∈ N' ⊓ K := ⟨hJN (hEJ hr), hrK⟩
  have hwO : r⁻¹ * k ∈ O := by
    have h1 : r⁻¹ * k = (r⁻¹ * z * r) * z⁻¹ := by rw [hkzr]; group
    rw [h1]
    refine O.mul_mem ?_ (O.inv_mem hz.2)
    have := (Subgroup.mem_normalizer_iff.1 (hOn (hKI hrK)) z).1 hz.2
    have h2 := (Subgroup.mem_normalizer_iff.1 (hOn (hKI (K.inv_mem hrK))) z).1 hz.2
    simpa using h2
  have hwK : r⁻¹ * k ∈ GLAPPrimeCoreOf 3 K :=
    le_glaPPrimeCoreOf_of_inf hp3 (fun g hg => hOn (hKI hg)) ⟨K.mul_mem (K.inv_mem hrK) hk, hwO⟩
  have : k = r * (r⁻¹ * k) := by group
  rw [this]
  exact ((N' ⊓ K) ⊔ GLAPPrimeCoreOf 3 K).mul_mem ((le_sup_left : N' ⊓ K ≤ _) hrN)
    ((le_sup_right : GLAPPrimeCoreOf 3 K ≤ _) hwK)

end CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710
