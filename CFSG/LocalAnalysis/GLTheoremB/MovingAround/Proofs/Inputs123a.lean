module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts3
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims126
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs123a

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk autBar barOf innerAut)
open scoped Pointwise

section Aut

variable {Y : Type*} [Group Y]

theorem mem_center_map (φ : MulAut Y) {z : Y} (hz : z ∈ Subgroup.center Y) :
    φ z ∈ Subgroup.center Y := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨h, rfl⟩ := φ.surjective g
  rw [← map_mul, ← map_mul, hz h]

@[expose] noncomputable def centerRes (Y : Type*) [Group Y] :
    MulAut Y →* MulAut ↥(Subgroup.center Y) where
  toFun φ :=
    { toFun := fun z => ⟨φ z.1, mem_center_map φ z.2⟩
      invFun := fun z => ⟨φ.symm z.1, mem_center_map φ.symm z.2⟩
      left_inv := fun z => Subtype.ext (φ.symm_apply_apply z.1)
      right_inv := fun z => Subtype.ext (φ.apply_symm_apply z.1)
      map_mul' := fun z w => Subtype.ext (map_mul φ z.1 w.1) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem centerRes_apply (φ : MulAut Y) (z : ↥(Subgroup.center Y)) :
    ((centerRes Y φ z : ↥(Subgroup.center Y)) : Y) = φ z.1 := rfl

theorem mul_conj_mul_inv (φ : MulAut Y) (y : Y) :
    φ * MulAut.conj y * φ⁻¹ = MulAut.conj (φ y) := by
  ext z
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem inv_mul_apply_mem_center {δ : MulAut Y} {y : Y}
    (h : MulAut.conj y * δ = δ * MulAut.conj y) : y⁻¹ * δ y ∈ Subgroup.center Y := by
  apply Lemma123.mem_center_of_conj_eq_one
  have h1 : MulAut.conj (δ y) = MulAut.conj y := by
    rw [← mul_conj_mul_inv, ← h, mul_inv_cancel_right]
  rw [map_mul, map_inv, h1, inv_mul_cancel]

theorem le_normalizer_of_conj {S Q : Subgroup Y} (h : ∀ g ∈ S, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) :
    S ≤ Subgroup.normalizer (Q : Set Y) := fun g hg =>
  Lemma123.mem_normalizer_of_conj_mem (h g hg) (h g⁻¹ (S.inv_mem hg))

theorem conj_mem_of_sup {P R T : Subgroup Y} {g : Y} (h1 : ∀ x ∈ P, g * x * g⁻¹ ∈ T)
    (h2 : ∀ x ∈ R, g * x * g⁻¹ ∈ T) : ∀ x ∈ P ⊔ R, g * x * g⁻¹ ∈ T := by
  intro x hx
  have hle : P ⊔ R ≤ T.comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun y hy => Subgroup.mem_comap.2 (by simpa [MulAut.conj_apply] using h1 y hy))
      (fun y hy => Subgroup.mem_comap.2 (by simpa [MulAut.conj_apply] using h2 y hy))
  simpa [MulAut.conj_apply] using Subgroup.mem_comap.1 (hle hx)

theorem eq_one_of_isPGroup_of_pow_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Y}
    (hS : IsPGroup p S) {g : Y} (hg : g ∈ S) {m : ℕ} (hgm : g ^ (2 ^ m) = 1) : g = 1 := by
  obtain ⟨j, hj⟩ := hS ⟨g, hg⟩
  have hj' : g ^ (p ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime (p ^ j) (2 ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj')
    (orderOf_dvd_of_pow_eq_one hgm))

end Aut

section Delta

variable {G : Type} [Group G] [Finite G]

theorem deltaImage_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X D K : Subgroup G} (hKX : K ≤ X)
    (hDel : IsElemAbelian p D) :
    Lemma123.DeltaImage p X D K ≤
      localDeltaTwoIn (innerAut (barOf p K) ⊔ Lemma123.DeltaImage p X D K) (autBar p D K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hN
  set W : Subgroup (MulAut (barOf p K)) := Lemma123.DeltaImage p X D K with hW
  set I : Subgroup (MulAut (barOf p K)) := innerAut (barOf p K) with hI
  unfold localDeltaTwoIn
  refine le_iInf fun δ => le_iInf fun hδ => le_iInf fun hδ1 => ?_
  obtain ⟨dN, hdD, rfl⟩ := hδ
  have hdD' : (dN : G) ∈ D := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hdD)).1
  have hd1 : (dN : G) ≠ 1 := by
    intro h
    apply hδ1
    have : dN = 1 := Subtype.ext h
    rw [this, map_one]
  set d : G := (dN : G) with hd
  set δ : MulAut (barOf p K) := barAut p K dN with hδdef
  have hdp : d ^ p = 1 := hDel.2 d hdD'
  set C : Subgroup G := X ⊓ Subgroup.centralizer ({d} : Set G) with hC
  set O : Subgroup G := pCoreOf 2 C with hO
  have hΔO : localDeltaTwoIn X D ≤ O :=
    (iInf_le _ d).trans ((iInf_le _ hdD').trans (iInf_le _ hd1))
  have hOC : O ≤ C := CFSG.LieType.BorelTits.pCoreOf_le 2 C
  have hO2 : IsPGroup 2 ↥O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  have hCO : C ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hπcomm : ∀ x : ↥N, (x : G) ∈ Subgroup.centralizer ({d} : Set G) →
      barAut p K x * δ = δ * barAut p K x := by
    intro x hx
    rw [hδdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hx)
  have hWmem : ∀ ω ∈ W, ∃ w : ↥N, (w : G) ∈ O ∧ barAut p K w = ω := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w, hΔO (Subgroup.mem_subgroupOf.1 hw), rfl⟩
  have hWC : W ≤ Subgroup.centralizer ({δ} : Set _) := by
    intro ω hω
    obtain ⟨w, hw, rfl⟩ := hWmem ω hω
    exact Subgroup.mem_centralizer_singleton_iff.2 (hπcomm w (hOC hw).2)
  have hW2 : IsPGroup 2 ↥W :=
    ((hO2.to_le hΔO).comap_subtype (K := N)).map (barAut p K)
  set A : Subgroup (MulAut (barOf p K)) :=
    ((K ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf N).map (barAut p K) with hA
  have hKC : ∀ x : ↥N, x ∈ (K ⊓ Subgroup.centralizer ({d} : Set G)).subgroupOf N →
      (x : G) ∈ K ∧ (x : G) ∈ C := by
    intro x hx
    have hx' := Subgroup.mem_subgroupOf.1 hx
    exact ⟨hx'.1, hKX hx'.1, hx'.2⟩
  have hAI : A ≤ I := by
    rintro _ ⟨x, hx, rfl⟩
    have hxK : (x : G) ∈ K := (hKC x hx).1
    rw [show x = ⟨(x : G), x.2⟩ from rfl, Lemma123.barAut_of_mem hxK x.2]
    exact ⟨_, rfl⟩
  have hAC : A ≤ Subgroup.centralizer ({δ} : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hπcomm x (hKC x hx).2.2)
  have hWA : ∀ ω ∈ W, ∀ a ∈ A, ω * a * ω⁻¹ ∈ A := by
    intro ω hω a ha
    obtain ⟨w, hw, rfl⟩ := hWmem ω hω
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨hxK, hxC⟩ := hKC x hx
    have hwC : (w : G) ∈ C := hOC hw
    refine ⟨w * x * w⁻¹, Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩, by simp [map_mul, map_inv]⟩
    · exact (Subgroup.mem_normalizer_iff.1 w.2 x).1 hxK
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwC.2 hxC.2) (Subgroup.inv_mem _ hwC.2)
  have hWnA : W ≤ Subgroup.normalizer (A : Set _) := le_normalizer_of_conj hWA
  set Q₀ : Subgroup G := (K ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ O with hQ₀
  set A₀ : Subgroup (MulAut (barOf p K)) := (Q₀.subgroupOf N).map (barAut p K) with hA₀
  have hA₀A : A₀ ≤ A := Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
  have hA₀n : A ≤ Subgroup.normalizer (A₀ : Set _) := by
    refine le_normalizer_of_conj ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨q, hq, rfl⟩
    obtain ⟨hxK, hxC⟩ := hKC x hx
    have hq' := Subgroup.mem_subgroupOf.1 hq
    obtain ⟨⟨hqK, hqd⟩, hqO⟩ := hq'
    refine ⟨x * q * x⁻¹, Subgroup.mem_subgroupOf.2 ⟨⟨?_, ?_⟩, ?_⟩, by simp [map_mul, map_inv]⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxK hqK) (Subgroup.inv_mem _ hxK)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxC.2 hqd) (Subgroup.inv_mem _ hxC.2)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hCO hxC) q).1 hqO
  have hA₀2 : IsPGroup 2 ↥A₀ :=
    ((hO2.to_le (inf_le_right : Q₀ ≤ O)).comap_subtype (K := N)).map (barAut p K)
  have hA₀P : A₀ ≤ pCoreOf 2 A :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hA₀A hA₀n hA₀2
  have hcommAW : ∀ a ∈ A, ∀ ω ∈ W, a * ω * a⁻¹ * ω⁻¹ ∈ pCoreOf 2 A := by
    intro a ha ω hω
    obtain ⟨w, hw, rfl⟩ := hWmem ω hω
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨hxK, hxC⟩ := hKC x hx
    have hwC : (w : G) ∈ C := hOC hw
    apply hA₀P
    refine ⟨x * w * x⁻¹ * w⁻¹, Subgroup.mem_subgroupOf.2 ⟨⟨?_, ?_⟩, ?_⟩, by simp [map_mul, map_inv]⟩
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 : (w : G) * (x : G)⁻¹ * (w : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 w.2 _).1 (K.inv_mem hxK)
      have h2 := K.mul_mem hxK h1
      simpa [mul_assoc] using h2
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxC.2 hwC.2)
        (Subgroup.inv_mem _ hxC.2)) (Subgroup.inv_mem _ hwC.2)
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 : (x : G) * (w : G) * (x : G)⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.1 (hCO hxC) _).1 hw
      exact O.mul_mem h1 (O.inv_mem hw)
  have hWnP : W ≤ Subgroup.normalizer (pCoreOf 2 A : Set _) :=
    hWnA.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A)
  set Q : Subgroup (MulAut (barOf p K)) := pCoreOf 2 A ⊔ W with hQ
  set B : Subgroup (MulAut (barOf p K)) := A ⊔ W with hB
  have hQ2 : IsPGroup 2 ↥Q :=
    IsPGroup.to_sup_of_normal_left' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A) hW2 hWnP
  have hAP : A ≤ Subgroup.normalizer (pCoreOf 2 A : Set _) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A
  have hBQ : B ≤ Subgroup.normalizer (Q : Set _) := by
    refine sup_le (le_normalizer_of_conj fun a ha => conj_mem_of_sup ?_ ?_)
      (le_normalizer_of_conj fun ω hω => conj_mem_of_sup ?_ ?_)
    · intro q hq
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hAP ha) q).1 hq)
    · intro ω hω
      have h := Q.mul_mem (Subgroup.mem_sup_left (hcommAW a ha ω hω)) (Subgroup.mem_sup_right hω)
      simpa [mul_assoc] using h
    · intro q hq
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.1 (hWnP hω) q).1 hq)
    · intro ω' hω'
      exact Subgroup.mem_sup_right (W.mul_mem (W.mul_mem hω hω') (W.inv_mem hω))
  have hQB : Q ≤ B := sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans le_sup_left) le_sup_right
  have hWB : W ≤ pCoreOf 2 B :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQB hBQ hQ2)
  have hZ : ∀ ω ∈ W, ∀ z ∈ Subgroup.center (barOf p K), ω z = z := by
    have hR : IsPGroup p ↥(Subgroup.center (barOf p K)) :=
      SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot hp (glaPPrimeCore_quotient_eq_bot hp)
    set Z : Subgroup (MulAut (barOf p K)) := Subgroup.zpowers δ with hZdef
    have hdNp : dN ^ p = 1 := Subtype.ext (by simpa using hdp)
    have hδp : δ ^ p = 1 := by rw [hδdef, ← map_pow, hdNp, map_one]
    have hZp : IsPGroup p ↥Z := l119_isPGroup_zpowers hδp
    have hWp : ¬ p ∣ Nat.card ↥W := Lemma123.not_dvd_card_of_isPGroup_two hp hp2 hW2
    let α : ↥W →* MulAut ↥(Subgroup.center (barOf p K)) := (centerRes (barOf p K)).comp W.subtype
    let β : ↥Z →* MulAut ↥(Subgroup.center (barOf p K)) := (centerRes (barOf p K)).comp Z.subtype
    have hαβ : ∀ a b, α a * β b = β b * α a := by
      intro a b
      show centerRes _ (a : MulAut (barOf p K)) * centerRes _ (b : MulAut (barOf p K)) =
        centerRes _ (b : MulAut (barOf p K)) * centerRes _ (a : MulAut (barOf p K))
      rw [← map_mul, ← map_mul]
      congr 1
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
      rw [← hn]
      have hc : Commute (a : MulAut (barOf p K)) δ :=
        Subgroup.mem_centralizer_singleton_iff.1 (hWC a.2)
      exact (hc.zpow_right n).eq
    have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
      intro a r hr
      have hrδ : δ (r : barOf p K) = r := by
        have h := congrArg Subtype.val (hr ⟨δ, Subgroup.mem_zpowers δ⟩)
        simpa [β, centerRes_apply] using h
      obtain ⟨w, hw, hwa⟩ := hWmem a a.2
      obtain ⟨y, hyC, hyr⟩ := AltFacts3.exists_fixed_lift hp dN.2 hdp hrδ
      apply Subtype.ext
      show (a : MulAut (barOf p K)) (r : barOf p K) = r
      have hyCC : (y : G) ∈ C := ⟨hKX y.2, hyC⟩
      have hcO : (w : G) * y * (w : G)⁻¹ * (y : G)⁻¹ ∈ O := by
        have h1 : (y : G) * (w : G)⁻¹ * (y : G)⁻¹ ∈ O :=
          (Subgroup.mem_normalizer_iff.1 (hCO hyCC) _).1 (O.inv_mem hw)
        have h2 := O.mul_mem hw h1
        simpa [mul_assoc] using h2
      obtain ⟨m, hm⟩ := hO2 ⟨_, hcO⟩
      have hm' : ((w : G) * y * (w : G)⁻¹ * (y : G)⁻¹) ^ (2 ^ m) = 1 := by
        simpa using congrArg Subtype.val hm
      set yw : ↥K := K.normalizerMonoidHom w y with hyw
      have hywc : ((yw * y⁻¹ : ↥K) : G) = (w : G) * y * (w : G)⁻¹ * (y : G)⁻¹ := by
        simp [hyw, Subgroup.normalizerMonoidHom_apply_apply_coe, mul_assoc]
      have hg : (a : MulAut (barOf p K)) (r : barOf p K) * (r : barOf p K)⁻¹ =
          QuotientGroup.mk (yw * y⁻¹) := by
        rw [← hwa, ← hyr, barAut_mk, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have hgZ : (a : MulAut (barOf p K)) (r : barOf p K) * (r : barOf p K)⁻¹ ∈
          Subgroup.center (barOf p K) :=
        Subgroup.mul_mem _ (mem_center_map _ r.2) (Subgroup.inv_mem _ r.2)
      have hgpow : ((a : MulAut (barOf p K)) (r : barOf p K) * (r : barOf p K)⁻¹) ^ (2 ^ m) = 1 := by
        rw [hg, ← QuotientGroup.mk_pow]
        have h1 : (yw * y⁻¹) ^ (2 ^ m) = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hywc, hm']; rfl)
        rw [h1, QuotientGroup.mk_one]
      exact mul_inv_eq_one.1 (eq_one_of_isPGroup_of_pow_two hp hp2 hR hgZ hgpow)
    intro ω hω z hz
    have h := CFSG.GroupTheory.thompson_A_times_B hR hWp hZp α β hαβ hfix ⟨ω, hω⟩
    have h2 := congrArg (fun φ : MulAut ↥(Subgroup.center (barOf p K)) =>
      ((φ ⟨z, hz⟩ : ↥(Subgroup.center (barOf p K))) : barOf p K)) h
    simpa [α, centerRes_apply] using h2
  have hliftA : ∀ k : barOf p K, δ k = k → MulAut.conj k ∈ A := by
    intro k hk
    obtain ⟨y, hyC, rfl⟩ := AltFacts3.exists_fixed_lift hp dN.2 hdp hk
    refine ⟨⟨(y : G), Subgroup.le_normalizer y.2⟩, Subgroup.mem_subgroupOf.2 ⟨y.2, hyC⟩, ?_⟩
    exact Lemma123.barAut_of_mem y.2 _
  have hSI : ∀ ι ∈ I ⊓ Subgroup.centralizer ({δ} : Set _), ∀ b ∈ B, ι * b * ι⁻¹ ∈ B := by
    intro ι hι
    obtain ⟨⟨y, rfl⟩, hιC⟩ := Subgroup.mem_inf.1 hι
    have hyz : y⁻¹ * δ y ∈ Subgroup.center (barOf p K) :=
      inv_mul_apply_mem_center (Subgroup.mem_centralizer_singleton_iff.1 hιC)
    set z : barOf p K := y⁻¹ * δ y with hz
    have hδy : δ y = y * z := by rw [hz]; group
    have hzc : ∀ g : barOf p K, z * g = g * z := fun g => (Subgroup.mem_center_iff.1 hyz g).symm
    refine conj_mem_of_sup ?_ ?_
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨hxK, hxC⟩ := hKC x hx
      have hxδ : δ (QuotientGroup.mk (⟨(x : G), hxK⟩ : ↥K)) = QuotientGroup.mk (⟨(x : G), hxK⟩ : ↥K) := by
        rw [hδdef, barAut_mk]
        congr 1
        apply Subtype.ext
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        have hc : (x : G) * d = d * x := Subgroup.mem_centralizer_singleton_iff.1 hxC.2
        show d * (x : G) * d⁻¹ = x
        rw [← hc]
        group
      rw [show x = ⟨(x : G), x.2⟩ from rfl, Lemma123.barAut_of_mem hxK x.2]
      refine Subgroup.mem_sup_left ?_
      rw [← map_inv, ← map_mul, ← map_mul]
      apply hliftA
      rw [map_mul, map_mul, map_inv, hxδ, hδy]
      have := hzc (QuotientGroup.mk (⟨(x : G), hxK⟩ : ↥K))
      calc y * z * QuotientGroup.mk ⟨(x : G), hxK⟩ * (y * z)⁻¹
          = y * (z * QuotientGroup.mk ⟨(x : G), hxK⟩) * z⁻¹ * y⁻¹ := by group
        _ = y * QuotientGroup.mk ⟨(x : G), hxK⟩ * y⁻¹ := by rw [this]; group
    · intro ω hω
      have hωδ : ω * δ = δ * ω := Subgroup.mem_centralizer_singleton_iff.1 (hWC hω)
      have hmem : MulAut.conj y * ω * (MulAut.conj y)⁻¹ * ω⁻¹ ∈ A := by
        have e : MulAut.conj y * ω * (MulAut.conj y)⁻¹ * ω⁻¹ = MulAut.conj (y * (ω y)⁻¹) := by
          rw [map_mul, map_inv, ← mul_conj_mul_inv ω y]
          group
        rw [e]
        apply hliftA
        have h1 : δ (ω y) = ω (δ y) := by
          rw [← MulAut.mul_apply, ← hωδ, MulAut.mul_apply]
        rw [map_mul, map_inv, h1, hδy, map_mul, hZ ω hω z hyz]
        group
      have h := B.mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hω)
      simpa [mul_assoc] using h
  have hSIn : I ⊓ Subgroup.centralizer ({δ} : Set _) ≤ Subgroup.normalizer (B : Set _) :=
    le_normalizer_of_conj hSI
  set Cδ : Subgroup (MulAut (barOf p K)) := (I ⊔ W) ⊓ Subgroup.centralizer ({δ} : Set _) with hCδ
  have hBC : B ≤ Cδ := sup_le (le_inf (hAI.trans le_sup_left) hAC) (le_inf le_sup_right hWC)
  have hCB : Cδ ≤ Subgroup.normalizer (B : Set _) := by
    intro c hc
    obtain ⟨hcH, hcC⟩ := Subgroup.mem_inf.1 hc
    haveI : I.Normal := Lemma123.innerAut_normal (barOf p K)
    have hcm : c ∈ ((I : Subgroup (MulAut (barOf p K))) : Set (MulAut (barOf p K))) *
        ((W : Subgroup (MulAut (barOf p K))) : Set (MulAut (barOf p K))) := by
      rw [← Subgroup.normal_mul]
      exact hcH
    obtain ⟨ι, hι, ω, hω, rfl⟩ := hcm
    have hιC : ι ∈ Subgroup.centralizer ({δ} : Set _) := by
      have h := Subgroup.mul_mem _ hcC (Subgroup.inv_mem _ (hWC hω))
      simpa using h
    exact Subgroup.mul_mem _ (hSIn (Subgroup.mem_inf.2 ⟨hι, hιC⟩))
      (Subgroup.le_normalizer (Subgroup.mem_sup_right hω))
  have hBO : pCoreOf 2 B ≤ pCoreOf 2 Cδ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 B).trans hBC)
      (hCB.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B)
  exact hWB.trans hBO

theorem input19_1_O2_img_holds : Lemma123.Input19_1_O2_img := by
  intro G _ _ _ _ p hp hp2 _ _ X D _ hD K hK _
  exact deltaImage_le hp hp2 hK.1 hD.2.1

end Delta

section Transport

variable {Y Y' : Type*} [Group Y] [Group Y']

theorem map_pCoreOf_le [Finite Y] (f : Y →* Y') (S : Subgroup Y) :
    (pCoreOf 2 S).map f ≤ pCoreOf 2 (S.map f) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 S))
    (Lemma123.map_le_normalizer_map f (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S).map f)

theorem map_inf_centralizer (f : Y →* Y') (hf : Function.Injective f) (H : Subgroup Y) (δ : Y) :
    (H ⊓ Subgroup.centralizer ({δ} : Set Y)).map f =
      H.map f ⊓ Subgroup.centralizer ({f δ} : Set Y') := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hxH, hxC⟩, rfl⟩
    refine ⟨⟨x, hxH, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.1 hxC]
  · rintro _ ⟨⟨x, hxH, rfl⟩, hxC⟩
    refine ⟨x, ⟨hxH, Subgroup.mem_centralizer_singleton_iff.2 (hf ?_)⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 hxC

theorem map_localDeltaTwoIn_le [Finite Y] (f : Y →* Y') (hf : Function.Injective f) (H D : Subgroup Y) :
    (localDeltaTwoIn H D).map f ≤ localDeltaTwoIn (H.map f) (D.map f) := by
  unfold localDeltaTwoIn
  refine le_iInf fun δ' => le_iInf fun hδ' => le_iInf fun hδ'1 => ?_
  obtain ⟨δ, hδ, rfl⟩ := hδ'
  have hδ1 : δ ≠ 1 := fun h => hδ'1 (by rw [h, map_one])
  refine (Subgroup.map_mono ((iInf_le _ δ).trans ((iInf_le _ hδ).trans (iInf_le _ hδ1)))).trans ?_
  rw [← map_inf_centralizer f hf H δ]
  exact map_pCoreOf_le f _

theorem isLocallyOTwoBalanced_of_map [Finite Y] [Finite Y'] {p k : ℕ} (f : MulAut Y →* MulAut Y')
    (hf : Function.Injective f) (hinn : innerAut Y' ≤ (innerAut Y).map f) {A : Subgroup (MulAut Y)}
    (h : IsLocallyOTwoBalanced p k (A.map f)) : IsLocallyOTwoBalanced p k A := by
  intro D hD H hH hDH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hD' : IsEkIn p k (A.map f) (D.map f) :=
    ⟨Subgroup.map_mono hDA, CFSG.SectionRank.isElemAbelian_map hDel f,
      by rw [Subgroup.card_map_of_injective hf, hDc]⟩
  have h0 := h _ hD' _ (hinn.trans (Subgroup.map_mono hH)) (Lemma123.map_le_normalizer_map f hDH)
  have hle := map_localDeltaTwoIn_le f hf H D
  rw [h0] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ hf).1 (le_bot_iff.1 hle)

theorem isWeaklyLocallyOTwoBalanced_of_map [Finite Y] [Finite Y'] {p k : ℕ} (f : MulAut Y →* MulAut Y')
    (hf : Function.Injective f) (hinn : innerAut Y' ≤ (innerAut Y).map f) {A : Subgroup (MulAut Y)}
    (h : IsWeaklyLocallyOTwoBalanced p k (A.map f)) : IsWeaklyLocallyOTwoBalanced p k A := by
  intro D hD H hH hAH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hD' : IsEkIn p k (A.map f) (D.map f) :=
    ⟨Subgroup.map_mono hDA, CFSG.SectionRank.isElemAbelian_map hDel f,
      by rw [Subgroup.card_map_of_injective hf, hDc]⟩
  have h0 := h _ hD' _ (hinn.trans (Subgroup.map_mono hH)) (Lemma123.map_le_normalizer_map f hAH)
  have hle : (⁅localDeltaTwoIn H D, A⁆).map f ≤ ⁅localDeltaTwoIn (H.map f) (D.map f), A.map f⁆ := by
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono (map_localDeltaTwoIn_le f hf H D) le_rfl
  rw [h0] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ hf).1 (le_bot_iff.1 hle)

theorem isLocallyOTwoBalancedWrtP_of_map [Finite Y] [Finite Y'] {p k : ℕ} (f : MulAut Y →* MulAut Y')
    (hf : Function.Injective f) (hinn : innerAut Y' ≤ (innerAut Y).map f)
    (h : IsLocallyOTwoBalancedWrtP p k Y') : IsLocallyOTwoBalancedWrtP p k Y :=
  fun A hA => isLocallyOTwoBalanced_of_map f hf hinn (h _ (CFSG.SectionRank.isElemAbelian_map hA f))

theorem isWeaklyLocallyOTwoBalancedWrtP_of_map [Finite Y] [Finite Y'] {p k : ℕ}
    (f : MulAut Y →* MulAut Y') (hf : Function.Injective f) (hinn : innerAut Y' ≤ (innerAut Y).map f)
    (h : IsWeaklyLocallyOTwoBalancedWrtP p k Y') : IsWeaklyLocallyOTwoBalancedWrtP p k Y :=
  fun A hA => isWeaklyLocallyOTwoBalanced_of_map f hf hinn
    (h _ (CFSG.SectionRank.isElemAbelian_map hA f))

theorem congr_conj (e : Y ≃* Y') (y : Y) : MulAut.congr e (MulAut.conj y) = MulAut.conj (e y) := by
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem innerAut_le_map_congr (e : Y ≃* Y') :
    innerAut Y' ≤ (innerAut Y).map (MulAut.congr e).toMonoidHom := by
  rintro _ ⟨y', rfl⟩
  refine ⟨MulAut.conj (e.symm y'), ⟨_, rfl⟩, ?_⟩
  show MulAut.congr e (MulAut.conj (e.symm y')) = MulAut.conj y'
  rw [congr_conj, MulEquiv.apply_symm_apply]

theorem isLocallyOTwoBalancedWrtP_congr [Finite Y] [Finite Y'] {p k : ℕ} (e : Y ≃* Y') :
    IsLocallyOTwoBalancedWrtP p k Y ↔ IsLocallyOTwoBalancedWrtP p k Y' :=
  ⟨isLocallyOTwoBalancedWrtP_of_map (MulAut.congr e.symm).toMonoidHom
      (MulAut.congr e.symm).injective (innerAut_le_map_congr e.symm),
    isLocallyOTwoBalancedWrtP_of_map (MulAut.congr e).toMonoidHom (MulAut.congr e).injective
      (innerAut_le_map_congr e)⟩

theorem innerAut_le_map_autQ (Y : Type*) [Group Y] :
    innerAut (Y ⧸ Subgroup.center Y) ≤ (innerAut Y).map (Lemma123.autQ Y) := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨MulAut.conj y, ⟨y, rfl⟩, Lemma123.autQ_conj y⟩

theorem isLocallyOTwoBalancedWrtP_of_quot [Finite Y] {p k : ℕ} (hY : commutator Y = ⊤)
    (h : IsLocallyOTwoBalancedWrtP p k (Y ⧸ Subgroup.center Y)) : IsLocallyOTwoBalancedWrtP p k Y :=
  isLocallyOTwoBalancedWrtP_of_map (Lemma123.autQ Y) (Lemma123.autQ_injective hY)
    (innerAut_le_map_autQ Y) h

theorem isWeaklyLocallyOTwoBalancedWrtP_of_quot [Finite Y] {p k : ℕ} (hY : commutator Y = ⊤)
    (h : IsWeaklyLocallyOTwoBalancedWrtP p k (Y ⧸ Subgroup.center Y)) :
    IsWeaklyLocallyOTwoBalancedWrtP p k Y :=
  isWeaklyLocallyOTwoBalancedWrtP_of_map (Lemma123.autQ Y) (Lemma123.autQ_injective hY)
    (innerAut_le_map_autQ Y) h

end Transport

section Four

open Equiv Equiv.Perm

@[expose] noncomputable def innerHom (Y : Type*) [Group Y] : Y ⧸ Subgroup.center Y →* MulAut Y :=
  QuotientGroup.lift (Subgroup.center Y) MulAut.conj fun _ hz =>
    MonoidHom.mem_ker.2 (Lemma123.conj_eq_one_of_mem_center hz)

theorem innerHom_injective (Y : Type*) [Group Y] : Function.Injective (innerHom Y) := by
  refine (injective_iff_map_eq_one _).2 fun q hq => ?_
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  exact (QuotientGroup.eq_one_iff y).2 (Lemma123.mem_center_of_conj_eq_one hq)

theorem innerHom_range (Y : Type*) [Group Y] : (innerHom Y).range = innerAut Y := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨y, rfl⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨(y : Y ⧸ Subgroup.center Y), rfl⟩

theorem localDeltaTwoIn_zpowers {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime) {d : M}
    (hd : orderOf d = p) (H : Subgroup M) :
    localDeltaTwoIn H (Subgroup.zpowers d) = pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set M)) := by
  have hd1 : d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hd
    exact hp.one_lt.ne hd
  apply le_antisymm
  · exact (iInf_le _ d).trans ((iInf_le _ (Subgroup.mem_zpowers d)).trans (iInf_le _ hd1))
  · refine le_iInf fun δ => le_iInf fun hδ => le_iInf fun hδ1 => ?_
    have hle : Subgroup.zpowers δ ≤ Subgroup.zpowers d := (Subgroup.zpowers_le).2 hδ
    have hδp : orderOf δ = p := by
      have h1 : orderOf δ ∣ p := by
        rw [← hd, ← Nat.card_zpowers, ← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime hp).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hδ1
      · exact h
    have heq : Subgroup.zpowers δ = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hδp, hd])
    have hC : Subgroup.centralizer ({δ} : Set M) = Subgroup.centralizer ({d} : Set M) := by
      ext x
      simp only [Subgroup.mem_centralizer_singleton_iff]
      constructor
      · intro hx
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (heq ▸ Subgroup.mem_zpowers d : d ∈ Subgroup.zpowers δ)
        rw [← hm]
        exact (Commute.zpow_right (hx : Commute x δ) m).eq
      · intro hx
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hδ
        rw [← hm]
        exact (Commute.zpow_right (hx : Commute x d) m).eq
    rw [hC]

variable {α : Type} [Fintype α] [DecidableEq α]

theorem pCoreOf_ne_bot_of_four {M : Type*} [Group M] [Finite M] (ψ : ↥(alternatingGroup α) →* M)
    (hψ : Function.Injective ψ) {σ : Perm α} (hσ : σ ∈ alternatingGroup α)
    (h4 : Fintype.card {i // σ i = i} = 4) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ ⟨σ, hσ⟩} : Set M)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : α → Prop := fun i => σ i = i with hP
  set L : Subgroup (Perm α) := AltFacts3.altOn P with hL
  have hLA : L ≤ alternatingGroup α := AltFacts3.altOn_le P
  set L' : Subgroup ↥(alternatingGroup α) := L.subgroupOf (alternatingGroup α) with hL'
  set T₀ : Subgroup ↥(alternatingGroup α) := pCoreOf 2 L' with hT₀
  set T : Subgroup M := T₀.map ψ with hT
  have hT₀ : T₀ ≠ ⊥ := by
    have hcard : Nat.card {i // P i} = 4 := by rw [Nat.card_eq_fintype_card]; exact h4
    haveI := alternatingGroup.normal_kleinFour hcard
    have hV2 : IsPGroup 2 ↥(alternatingGroup.kleinFour {i // P i}) := by
      refine IsPGroup.of_card (n := 2) ?_
      rw [alternatingGroup.kleinFour_card_of_card_eq_four hcard]
      norm_num
    have hVle : alternatingGroup.kleinFour {i // P i} ≤ CFSG.pCore 2 ↥(alternatingGroup {i // P i}) :=
      CFSG.LieType.BorelTits.le_pCore 2 inferInstance hV2
    have hVne : alternatingGroup.kleinFour {i // P i} ≠ ⊥ := by
      intro h
      have := alternatingGroup.kleinFour_card_of_card_eq_four hcard
      rw [h, Subgroup.card_bot] at this
      norm_num at this
    let e : ↥(alternatingGroup {i // P i}) ≃* ↥L' :=
      (AltFacts3.altOnEquiv P).trans (Subgroup.subgroupOfEquivOfLe hLA).symm
    have hcore : (CFSG.pCore 2 ↥(alternatingGroup {i // P i})).map e.toMonoidHom = CFSG.pCore 2 ↥L' :=
      CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
    intro hbot
    apply hVne
    have h1 : (alternatingGroup.kleinFour {i // P i}).map e.toMonoidHom ≤ CFSG.pCore 2 ↥L' :=
      hcore ▸ Subgroup.map_mono hVle
    have h2 : CFSG.pCore 2 ↥L' = ⊥ := by
      have h3 : (CFSG.pCore 2 ↥L').map L'.subtype = ⊥ := hbot
      exact (Subgroup.map_eq_bot_iff_of_injective _ L'.subtype_injective).1 h3
    rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ e.injective] at h1
    exact h1
  have hTne : T ≠ ⊥ := fun h => hT₀ ((Subgroup.map_eq_bot_iff_of_injective _ hψ).1 h)
  have hTle : T ≤ ψ.range ⊓ Subgroup.centralizer ({ψ ⟨σ, hσ⟩} : Set M) := by
    rintro _ ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have htL : (t : Perm α) ∈ L :=
      Subgroup.mem_subgroupOf.1 (CFSG.LieType.BorelTits.pCoreOf_le 2 L' ht)
    have hc := AltFacts3.comm_of_mem_altOn htL
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  have hnorm : ψ.range ⊓ Subgroup.centralizer ({ψ ⟨σ, hσ⟩} : Set M) ≤ Subgroup.normalizer (T : Set M) := by
    rintro _ ⟨⟨g, rfl⟩, hgC⟩
    have hgσ : (g : Perm α) * σ = σ * g := by
      have h1 : ψ (g * ⟨σ, hσ⟩) = ψ (⟨σ, hσ⟩ * g) := by
        rw [map_mul, map_mul]; exact Subgroup.mem_centralizer_singleton_iff.1 hgC
      exact congrArg Subtype.val (hψ h1)
    have hgP : ∀ x, P ((g : Perm α) x) ↔ P x := by
      intro x
      show σ ((g : Perm α) x) = (g : Perm α) x ↔ σ x = x
      rw [← Perm.mul_apply, ← hgσ, Perm.mul_apply]
      exact (g : Perm α).injective.eq_iff
    have hgL : g ∈ Subgroup.normalizer (L' : Set ↥(alternatingGroup α)) := by
      refine le_normalizer_of_conj (S := Subgroup.zpowers g) (fun g' hg' l hl => ?_) (Subgroup.mem_zpowers g)
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
      have hP' : ∀ x, P (((g ^ m : ↥(alternatingGroup α)) : Perm α) x) ↔ P x := by
        intro x
        have hc : Commute ((g : Perm α)) σ := hgσ
        rw [Subgroup.coe_zpow]
        show σ (((g : Perm α) ^ m) x) = ((g : Perm α) ^ m) x ↔ σ x = x
        rw [← Perm.mul_apply, ← (hc.zpow_left m).eq, Perm.mul_apply]
        exact ((g : Perm α) ^ m).injective.eq_iff
      rw [Subgroup.mem_subgroupOf] at hl ⊢
      simpa using AltFacts3.conj_mem_altOn P hP' hl
    have hgT₀ : g ∈ Subgroup.normalizer (T₀ : Set ↥(alternatingGroup α)) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L' hgL
    exact Lemma123.map_le_normalizer_map ψ (Subgroup.zpowers_le.2 hgT₀) ⟨g, Subgroup.mem_zpowers g, rfl⟩
  have hT2 : IsPGroup 2 ↥T := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L').map ψ
  intro hbot
  apply hTne
  have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTle hnorm hT2
  rw [hbot] at this
  exact le_bot_iff.1 this

theorem not_balanced_of_four {Y : Type*} [Group Y] [Finite Y] {n p : ℕ} (hp : p.Prime)
    (θ : (Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin n)) {σ : Perm (Fin n)}
    (hσ : σ ∈ alternatingGroup (Fin n)) (hσp : σ ^ p = 1) (hσ1 : σ ≠ 1)
    (h4 : Fintype.card {i // σ i = i} = 4) : ¬ IsLocallyOTwoBalancedWrtP p 1 Y := by
  intro hbal
  haveI : Fact p.Prime := ⟨hp⟩
  set ψ : ↥(alternatingGroup (Fin n)) →* MulAut Y := (innerHom Y).comp θ.symm.toMonoidHom with hψ
  have hψi : Function.Injective ψ := (innerHom_injective Y).comp θ.symm.injective
  have hψr : ψ.range = innerAut Y := by
    rw [← innerHom_range]
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨θ.symm a, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨θ q, by simp [hψ]⟩
  set d : MulAut Y := ψ ⟨σ, hσ⟩ with hd
  have hσo : orderOf (⟨σ, hσ⟩ : ↥(alternatingGroup (Fin n))) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hσp hσ1
  have hdo : orderOf d = p := by rw [hd, orderOf_injective ψ hψi]; exact hσo
  have hdp : d ^ p = 1 := by rw [← hdo]; exact pow_orderOf_eq_one d
  have hD : IsEkIn p 1 (Subgroup.zpowers d) (Subgroup.zpowers d) :=
    ⟨le_rfl, CFSG.Open.isElemAbelian_zpowers hdp, by rw [Nat.card_zpowers, hdo, pow_one]⟩
  have hdI : d ∈ innerAut Y := hψr ▸ ⟨_, rfl⟩
  have h0 := hbal _ (CFSG.Open.isElemAbelian_zpowers hdp) _ hD (innerAut Y) le_rfl
    ((Subgroup.zpowers_le.2 hdI).trans Subgroup.le_normalizer)
  rw [localDeltaTwoIn_zpowers hp hdo, ← hψr] at h0
  exact pCoreOf_ne_bot_of_four ψ hψi hσ h4 h0

end Four

section AltN

open Equiv Equiv.Perm

variable {α : Type} [Fintype α] [DecidableEq α]

theorem pow_eq_one_of_mem_uSub {σ u : Perm α} {p : ℕ} (hσ : σ ^ p = 1) (hu : u ∈ Claims126.uSub σ) :
    u ^ p = 1 := by
  ext x
  obtain ⟨k, hk⟩ := hu.2 x
  rw [Claims126.pow_apply_of_mem_uSub hu hk p, pow_mul, hσ, one_pow]

theorem uSub_le_alternatingGroup {σ : Perm α} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : σ ^ p = 1) :
    Claims126.uSub σ ≤ alternatingGroup α := by
  intro u hu
  rw [Perm.mem_alternatingGroup]
  have h := congrArg Perm.sign (pow_eq_one_of_mem_uSub hσ hu)
  rw [map_pow, map_one] at h
  rcases Int.units_eq_one_or (Perm.sign u) with h1 | h1
  · exact h1
  · rw [h1, (hp.odd_of_ne_two hp2).neg_one_pow] at h
    exact absurd h (by decide)

theorem isPGroup_uSub_p {σ : Perm α} {p : ℕ} (hσ : σ ^ p = 1) : IsPGroup p ↥(Claims126.uSub σ) :=
  fun u => ⟨1, Subtype.ext (by simpa using pow_eq_one_of_mem_uSub hσ u.2)⟩

theorem apply_eq_of_pow_two {σ x : Perm α} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : σ ^ p = 1)
    (hxσ : x * σ = σ * x) {e : ℕ} (hxe : x ^ (2 ^ e) = 1) {y : α} (hy : σ y ≠ y) {k : ℕ}
    (hk : x y = (σ ^ k) y) : x y = y := by
  have hpow : ∀ m : ℕ, (x ^ m) y = (σ ^ (m * k)) y := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hc : x ^ m * σ ^ k = σ ^ k * x ^ m := (Commute.pow_pow (hxσ : Commute x σ) m k).eq
      rw [pow_succ, Perm.mul_apply, hk, ← Perm.mul_apply, hc, Perm.mul_apply, ih, ← Perm.mul_apply,
        ← pow_add]
      congr 2
      ring
  have h1 : (σ ^ (2 ^ e * k)) y = y := by rw [← hpow, hxe]; rfl
  have hpk : p ∣ k := by
    by_contra hpk
    have hcop : Nat.Coprime (2 ^ e * k) p :=
      Nat.coprime_mul_iff_left.2 ⟨Nat.Coprime.pow_left _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)),
        Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpk)⟩
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
    apply hy
    have h2 : (σ ^ (2 ^ e * k * m)) y = y := by
      rw [pow_mul]
      exact Perm.pow_apply_eq_self_of_apply_eq_self h1 m
    have h3 : σ ^ (2 ^ e * k * m) = σ := by
      rw [← Nat.mod_add_div (2 ^ e * k * m) p, hm, pow_add, pow_mul, hσ, one_pow, mul_one, pow_one]
    rwa [h3] at h2
  obtain ⟨k', rfl⟩ := hpk
  rw [hk, pow_mul, hσ, one_pow]
  rfl

theorem pCoreOf_eq_bot_of_card_fix {σ : Perm α} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hσ : σ ^ p = 1)
    {H : Subgroup (Perm α)} (hH : alternatingGroup α ≤ H)
    (h2 : Fintype.card {i // σ i = i} ≠ 2) (h4 : Fintype.card {i // σ i = i} ≠ 4) :
    pCoreOf 2 (H ⊓ Subgroup.centralizer ({σ} : Set (Perm α))) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  set S : Subgroup (Perm α) := H ⊓ Subgroup.centralizer ({σ} : Set (Perm α)) with hS
  set T : Subgroup (Perm α) := pCoreOf 2 S with hT
  have hTS : T ≤ S := CFSG.LieType.BorelTits.pCoreOf_le 2 S
  have hSN : S ≤ Subgroup.normalizer (T : Set (Perm α)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S
  have hT2 : IsPGroup 2 ↥T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S
  have hTe : ∀ x ∈ T, ∃ e : ℕ, x ^ (2 ^ e) = 1 := fun x hx => by
    obtain ⟨e, he⟩ := hT2 ⟨x, hx⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hTσ : ∀ x ∈ T, x * σ = σ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.1 (hTS hx).2
  have hcommT : ∀ x ∈ T, ∀ g ∈ S, x * g * x⁻¹ * g⁻¹ ∈ T := by
    intro x hx g hg
    have h1 : g * x⁻¹ * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hSN hg) _).1 (T.inv_mem hx)
    simpa [mul_assoc] using T.mul_mem hx h1
  set U : Subgroup (Perm α) := Claims126.uSub σ with hU
  have hUS : U ≤ S := fun u hu =>
    ⟨hH (uSub_le_alternatingGroup hp hp2 hσ hu), Subgroup.mem_centralizer_singleton_iff.2 hu.1⟩
  have hTU : ∀ x ∈ T, ∀ u ∈ U, x * u = u * x := by
    intro x hx u hu
    have hcU : x * u * x⁻¹ * u⁻¹ ∈ U :=
      U.mul_mem (Claims126.conj_mem_uSub (hTσ x hx) hu) (U.inv_mem hu)
    obtain ⟨e, he⟩ := hTe _ (hcommT x hx u (hUS hu))
    have h1 := eq_one_of_isPGroup_of_pow_two hp hp2 (isPGroup_uSub_p hσ) hcU he
    calc x * u = (x * u * x⁻¹ * u⁻¹) * (u * x) := by group
      _ = u * x := by rw [h1, one_mul]
  have hTmov : ∀ x ∈ T, ∀ y, σ y ≠ y → x y = y := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := Claims126.exists_pow_of_comm_uSub (hTσ x hx) (hTU x hx) hy
    obtain ⟨e, he⟩ := hTe x hx
    exact apply_eq_of_pow_two hp hp2 hσ (hTσ x hx) he hy hk
  have hTfix : ∀ x ∈ T, ∀ y, σ y = y → σ (x y) = x y := by
    intro x hx y hy
    rw [← Perm.mul_apply, ← hTσ x hx, Perm.mul_apply, hy]
  set P : α → Prop := fun i => σ i = i with hP
  set L : Subgroup (Perm α) := AltFacts3.altOn P with hL
  have hLS : L ≤ S := fun l hl =>
    ⟨hH (AltFacts3.altOn_le P hl), Subgroup.mem_centralizer_singleton_iff.2 (AltFacts3.comm_of_mem_altOn hl)⟩
  have hTL : ∀ x ∈ T, ∀ l ∈ L, x * l * x⁻¹ ∈ L := by
    intro x hx l hl
    refine AltFacts3.conj_mem_altOn P (fun z => ?_) hl
    show σ (x z) = x z ↔ σ z = z
    rw [← Perm.mul_apply, ← hTσ x hx, Perm.mul_apply]
    exact x.injective.eq_iff
  have hcommL : ∀ x ∈ T, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ T ⊓ L := fun x hx l hl =>
    ⟨hcommT x hx l (hLS hl), L.mul_mem (hTL x hx l hl) (L.inv_mem hl)⟩
  have hcentL : T ⊓ L = ⊥ → ∀ x ∈ T, ∀ l ∈ L, x * l = l * x := by
    intro h0 x hx l hl
    have h1 := hcommL x hx l hl
    rw [h0, Subgroup.mem_bot] at h1
    calc x * l = (x * l * x⁻¹ * l⁻¹) * (l * x) := by group
      _ = l * x := by rw [h1, one_mul]
  set F : Finset α := Finset.univ.filter P with hF
  have hFc : F.card = Fintype.card {i // σ i = i} := (Fintype.card_subtype P).symm
  have hmemF : ∀ i, i ∈ F ↔ σ i = i := fun i => by simp [hF, hP]
  have hcardP : Nat.card {i // P i} = F.card := by rw [Nat.card_eq_fintype_card, hFc]
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  ext i
  rw [Perm.one_apply]
  by_cases hi : σ i = i
  swap
  · exact hTmov x hx i hi
  by_contra hxi
  set i' := x i with hi'
  have hi'F : σ i' = i' := hTfix x hx i hi
  have hii' : i ≠ i' := fun h => hxi h.symm
  have hr2 : 2 ≤ F.card :=
    Finset.one_lt_card.2 ⟨i, (hmemF i).2 hi, i', (hmemF i').2 hi'F, hii'⟩
  have hF2 : (F.erase i).erase i' ⊆ F := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hFe : ((F.erase i).erase i').card = F.card - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hii'.symm, (hmemF i').2 hi'F⟩),
      Finset.card_erase_of_mem ((hmemF i).2 hi)]
    omega
  rcases (show F.card = 3 ∨ 5 ≤ F.card by omega) with hr3 | hr5
  ·
    have hLc : Nat.card ↥L = 3 := by
      rw [← Nat.card_congr (AltFacts3.altOnEquiv P).toEquiv]
      haveI : Nontrivial {i // P i} := ⟨⟨⟨i, hi⟩, ⟨i', hi'F⟩, fun h => hii' (congrArg Subtype.val h)⟩⟩
      rw [nat_card_alternatingGroup, hcardP, hr3]
      rfl
    have hTL1 : T ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      obtain ⟨e, he⟩ := hTe y hy.1
      have h1 : orderOf y ∣ 3 := by
        have h3 := orderOf_dvd_natCard (⟨y, hy.2⟩ : ↥L)
        rwa [hLc, Subgroup.orderOf_mk] at h3
      exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
        (Nat.Coprime.pow_right e (by norm_num : Nat.Coprime 3 2)) h1 (orderOf_dvd_of_pow_eq_one he))
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 (by rw [hFe, hr3] : ((F.erase i).erase i').card = 1)
    have hkF : k ∈ (F.erase i).erase i' := by rw [hk]; exact Finset.mem_singleton_self k
    obtain ⟨hki', hkF'⟩ := Finset.mem_erase.1 hkF
    obtain ⟨hki, hkF''⟩ := Finset.mem_erase.1 hkF'
    have hkσ : σ k = k := (hmemF k).1 hkF''
    have hFall : ∀ z, σ z = z → z = i ∨ z = i' ∨ z = k := by
      intro z hz
      by_cases hzi : z = i
      · exact Or.inl hzi
      by_cases hzi' : z = i'
      · exact Or.inr (Or.inl hzi')
      have hz' : z ∈ (F.erase i).erase i' :=
        Finset.mem_erase.2 ⟨hzi', Finset.mem_erase.2 ⟨hzi, (hmemF z).2 hz⟩⟩
      rw [hk, Finset.mem_singleton] at hz'
      exact Or.inr (Or.inr hz')
    obtain ⟨c, hcdef⟩ : ∃ c : Perm α, c = swap i i' * swap i k := ⟨_, rfl⟩
    have hc : c ∈ L := hcdef ▸
      AltFacts3.swap_mul_swap_mem_altOn P hi hi'F hkσ hii' (Ne.symm hki) (Ne.symm hki')
    have hxc := hcentL hTL1 x hx _ hc
    have hci : c i = k := by
      rw [hcdef, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hki hki']
    have hck : c k = i' := by
      rw [hcdef, Perm.mul_apply, swap_apply_right, swap_apply_left]
    have hci' : c i' = i := by
      rw [hcdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hii') (Ne.symm hki'), swap_apply_right]
    have hxk : x k = i := by
      have h1 := congrArg (fun f : Perm α => f i) hxc
      simp only [Perm.mul_apply] at h1
      rw [hci, ← hi', hci'] at h1
      exact h1
    have hxi' : x i' = k := by
      have h1 := congrArg (fun f : Perm α => f k) hxc
      simp only [Perm.mul_apply] at h1
      rw [hck, hxk, hci] at h1
      exact h1
    have hx3 : x ^ 3 = 1 := by
      ext z
      rw [Perm.one_apply]
      by_cases hz : σ z = z
      · rcases hFall z hz with rfl | rfl | rfl
        · simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply]
          rw [← hi', hxi', hxk]
        · simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply]
          rw [hxi', hxk, ← hi']
        · simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply]
          rw [hxk, ← hi', hxi']
      · exact Perm.pow_apply_eq_self_of_apply_eq_self (hTmov x hx z hz) 3
    obtain ⟨e, he⟩ := hTe x hx
    have hx1 : x = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right e (by norm_num : Nat.Coprime 3 2)) (orderOf_dvd_of_pow_eq_one hx3)
      (orderOf_dvd_of_pow_eq_one he))
    exact hxi (by rw [hi', hx1, Perm.one_apply])
  ·
    have hTL1 : T ⊓ L = ⊥ := by
      haveI : IsSimpleGroup ↥(alternatingGroup {i // P i}) :=
        alternatingGroup.isSimpleGroup (by rw [hcardP]; exact hr5)
      haveI : IsSimpleGroup ↥L := (AltFacts3.altOnEquiv P).isSimpleGroup_congr.1 inferInstance
      have hN : ((T ⊓ L).subgroupOf L).Normal := by
        refine ⟨fun y hy l => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hy ⊢
        refine ⟨?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.1 (hSN (hLS l.2)) _).1 hy.1
        · exact L.mul_mem (L.mul_mem l.2 hy.2) (L.inv_mem l.2)
      rcases hN.eq_bot_or_eq_top with hb | ht
      · rw [eq_bot_iff]
        intro y hy
        have h1 : (⟨y, hy.2⟩ : ↥L) ∈ (T ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.2 hy
        rw [hb, Subgroup.mem_bot] at h1
        exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
      · exfalso
        obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 (by rw [hFe]; omega :
          1 < ((F.erase i).erase i').card)
        have hjF := (hmemF j).1 (hF2 hj)
        have hkF := (hmemF k).1 (hF2 hk)
        have hji : j ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hj).2).1
        have hki : k ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hk).2).1
        have hc : swap i j * swap i k ∈ L :=
          AltFacts3.swap_mul_swap_mem_altOn P hi hjF hkF (Ne.symm hji) (Ne.symm hki) hjk
        have hcT : swap i j * swap i k ∈ T := by
          have h1 : (⟨_, hc⟩ : ↥L) ∈ (T ⊓ L).subgroupOf L := by rw [ht]; exact Subgroup.mem_top _
          exact (Subgroup.mem_subgroupOf.1 h1).1
        obtain ⟨e, he⟩ := hTe _ hcT
        have h3 : orderOf (swap i j * swap i k) = 3 :=
          (Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hji) (Ne.symm hki) hjk).orderOf
        have h3' : 3 ∣ 2 ^ e := h3 ▸ orderOf_dvd_of_pow_eq_one he
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
          (Nat.prime_three.dvd_of_dvd_pow h3')
        omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.1 (by rw [hFe]; omega :
      1 < ((F.erase i).erase i').card)
    have hjF := (hmemF j).1 (hF2 hj)
    have hkF := (hmemF k).1 (hF2 hk)
    have hji' : j ≠ i' := (Finset.mem_erase.1 hj).1
    have hki' : k ≠ i' := (Finset.mem_erase.1 hk).1
    have hji : j ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hj).2).1
    have hki : k ≠ i := (Finset.mem_erase.1 (Finset.mem_erase.1 hk).2).1
    obtain ⟨c, hcdef⟩ : ∃ c : Perm α, c = swap i j * swap i k := ⟨_, rfl⟩
    have hc : c ∈ L := hcdef ▸
      AltFacts3.swap_mul_swap_mem_altOn P hi hjF hkF (Ne.symm hji) (Ne.symm hki) hjk
    have hxc := hcentL hTL1 x hx _ hc
    have hci : c i = k := by
      rw [hcdef, Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hki hjk.symm]
    have hci' : c i' = i' := by
      rw [hcdef, Perm.mul_apply, swap_apply_of_ne_of_ne (Ne.symm hii') (Ne.symm hki'),
        swap_apply_of_ne_of_ne (Ne.symm hii') (Ne.symm hji')]
    have h1 := congrArg (fun f : Perm α => f i) hxc
    simp only [Perm.mul_apply] at h1
    rw [hci, ← hi', hci', hi'] at h1
    exact hki (x.injective h1)

theorem exists_perm_fix {n p r m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hm : 0 < m) (hn : n = r + m * p) :
    ∃ σ : Perm (Fin n), σ ∈ alternatingGroup (Fin n) ∧ σ ^ p = 1 ∧ σ ≠ 1 ∧
      Fintype.card {i // σ i = i} = r := by
  classical
  obtain ⟨σ, hσ⟩ := (Perm.exists_with_cycleType_iff (α := Fin n) (m := Multiset.replicate m p)).2
    ⟨by rw [Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin]; omega,
      fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; exact hp.two_le⟩
  refine ⟨σ, ?_, ?_, ?_, ?_⟩
  · rw [Perm.mem_alternatingGroup, Perm.sign_of_cycleType, hσ, Multiset.sum_replicate,
      Multiset.card_replicate, smul_eq_mul]
    have hev : Even (m * p + m) := by
      rw [show m * p + m = m * (p + 1) by ring]
      exact (hp.odd_of_ne_two hp2).add_one.mul_left m
    exact hev.neg_one_pow
  · rw [← orderOf_dvd_iff_pow_eq_one, ← Perm.lcm_cycleType, hσ]
    exact Multiset.lcm_dvd.2 fun b hb => by rw [Multiset.eq_of_mem_replicate hb]
  · intro h
    rw [h, Perm.cycleType_one] at hσ
    have h1 := congrArg Multiset.card hσ
    rw [Multiset.card_zero, Multiset.card_replicate] at h1
    omega
  · have h1 := Perm.card_fixedPoints σ
    rw [hσ, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at h1
    have h2 : Fintype.card {i // σ i = i} = Fintype.card (Function.fixedPoints σ) :=
      Fintype.card_congr (Equiv.refl _)
    rw [h2, h1]
    omega

theorem pCoreOf_ne_bot_of_two {M : Type} [Group M] [Finite M] (ψ : Perm α →* M)
    (hψ : Function.Injective ψ) {σ : Perm α} (h2 : Fintype.card {i // σ i = i} = 2) :
    pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer ({ψ σ} : Set M)) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : (Finset.univ.filter fun i => σ i = i).card = 2 := by
    rw [← Fintype.card_subtype]; exact h2
  obtain ⟨a, b, hab, hFab⟩ := Finset.card_eq_two.1 hF
  have hmem : ∀ z, σ z = z ↔ z = a ∨ z = b := fun z => by
    have h1 := congrArg (z ∈ ·) hFab
    simpa using h1
  have ha : σ a = a := (hmem a).2 (Or.inl rfl)
  have hb : σ b = b := (hmem b).2 (Or.inr rfl)
  set t : Perm α := swap a b with ht
  have hgt : ∀ g : Perm α, g * σ = σ * g → g * t * g⁻¹ = t := by
    intro g hg
    have hfix : ∀ z, σ z = z → σ (g z) = g z := fun z hz => by
      rw [← Perm.mul_apply, ← hg, Perm.mul_apply, hz]
    rw [ht, ← Equiv.swap_apply_apply]
    rcases (hmem (g a)).1 (hfix a ha) with h1 | h1 <;>
      rcases (hmem (g b)).1 (hfix b hb) with h2 | h2
    · exact absurd (g.injective (h1.trans h2.symm)) hab
    · rw [h1, h2]
    · rw [h1, h2, Equiv.swap_comm]
    · exact absurd (g.injective (h1.trans h2.symm)) hab
  have htσ : t * σ = σ * t := by
    have h1 := hgt σ rfl
    calc t * σ = (σ * t * σ⁻¹) * σ := by rw [h1]
      _ = σ * t := by group
  set V : Subgroup M := Subgroup.zpowers (ψ t) with hV
  have hV2 : IsPGroup 2 ↥V :=
    l119_isPGroup_zpowers (p := 2) (x := ψ t) (by rw [← map_pow, ht, pow_two, Equiv.swap_mul_self, map_one])
  have hVne : V ≠ ⊥ := by
    intro h
    have h1 : ψ t ∈ V := Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at h1
    have ht1 : t = 1 := hψ (h1.trans (map_one ψ).symm)
    have h2 := congrArg (fun f : Perm α => f a) ht1
    simp only [ht, swap_apply_left, Perm.one_apply] at h2
    exact hab h2.symm
  have hVle : V ≤ ψ.range ⊓ Subgroup.centralizer ({ψ σ} : Set M) := by
    rw [hV, Subgroup.zpowers_le]
    refine ⟨⟨t, rfl⟩, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, htσ]
  have hnorm : ψ.range ⊓ Subgroup.centralizer ({ψ σ} : Set M) ≤ Subgroup.normalizer (V : Set M) := by
    rintro _ ⟨⟨g, rfl⟩, hgC⟩
    have hgσ : g * σ = σ * g :=
      hψ (by rw [map_mul, map_mul]; exact Subgroup.mem_centralizer_singleton_iff.1 hgC)
    have hc : ψ g * ψ t * (ψ g)⁻¹ = ψ t := by rw [← map_inv, ← map_mul, ← map_mul, hgt g hgσ]
    have hc' : Commute (ψ g) (ψ t) := by
      show ψ g * ψ t = ψ t * ψ g
      calc ψ g * ψ t = (ψ g * ψ t * (ψ g)⁻¹) * ψ g := by group
        _ = ψ t * ψ g := by rw [hc]
    refine le_normalizer_of_conj (S := Subgroup.zpowers (ψ g)) ?_ (Subgroup.mem_zpowers _)
    intro g' hg' v hv
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
    obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    rw [((hc'.zpow_left m).zpow_right m').eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ _
  intro hbot
  apply hVne
  have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVle hnorm hV2
  rw [hbot] at h1
  exact le_bot_iff.1 h1

theorem not_balanced_of_core {Y : Type*} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) {d : MulAut Y}
    (hd : orderOf d = p) {H : Subgroup (MulAut Y)} (hH : innerAut Y ≤ H) (hdH : d ∈ H)
    (hne : pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut Y))) ≠ ⊥) :
    ¬ IsLocallyOTwoBalancedWrtP p 1 Y := by
  intro hbal
  have hdp : d ^ p = 1 := by rw [← hd]; exact pow_orderOf_eq_one d
  have hD : IsEkIn p 1 (Subgroup.zpowers d) (Subgroup.zpowers d) :=
    ⟨le_rfl, CFSG.Open.isElemAbelian_zpowers hdp, by rw [Nat.card_zpowers, hd, pow_one]⟩
  have h0 := hbal _ (CFSG.Open.isElemAbelian_zpowers hdp) _ hD H hH
    ((Subgroup.zpowers_le.2 hdH).trans Subgroup.le_normalizer)
  rw [localDeltaTwoIn_zpowers hp hd] at h0
  exact hne h0

theorem not_balanced_alt_of_mod {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n)
    (h : n % p = 2 ∨ n % p = 4 % p) : ¬ IsLocallyOTwoBalancedWrtP p 1 ↥(alternatingGroup (Fin n)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rcases h with h2 | h4
  · have hdm := Nat.div_add_mod n p
    obtain ⟨σ, -, hσp, hσ1, hfix⟩ :=
      exists_perm_fix (n := n) (r := 2) (m := n / p) hp hp2 (by
        rcases Nat.eq_zero_or_pos (n / p) with h0 | h0
        · rw [h0, mul_zero, zero_add, h2] at hdm; omega
        · exact h0) (by rw [h2] at hdm; linarith [mul_comm p (n / p)])
    set ψ : Perm (Fin n) →* MulAut ↥(alternatingGroup (Fin n)) :=
      MulAut.conjNormal (H := alternatingGroup (Fin n)) with hψdef
    have hψ : Function.Injective ψ :=
      CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n (by omega)
    refine not_balanced_of_core hp (d := ψ σ) (H := ψ.range) ?_ ?_ ⟨σ, rfl⟩
      (pCoreOf_ne_bot_of_two ψ hψ hfix)
    · rw [orderOf_injective ψ hψ]; exact orderOf_eq_prime hσp hσ1
    · rintro _ ⟨a, rfl⟩
      refine ⟨(a : Perm (Fin n)), ?_⟩
      ext x
      simp [hψdef, MulAut.conjNormal_apply, MulAut.conj_apply]
  · have hsub : (n - 4) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq h4
    have hdm := Nat.div_add_mod (n - 4) p
    rw [hsub, add_zero] at hdm
    obtain ⟨σ, hσA, hσp, hσ1, hfix⟩ :=
      exists_perm_fix (n := n) (r := 4) (m := (n - 4) / p) hp hp2 (by
        rcases Nat.eq_zero_or_pos ((n - 4) / p) with h0 | h0
        · rw [h0, mul_zero] at hdm; omega
        · exact h0) (by rw [mul_comm] at hdm; omega)
    have hZ := AltFacts3.center_alt (m := n) (by omega)
    exact not_balanced_of_four hp ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      hσA hσp hσ1 hfix

theorem balanced_alt_of_not_mod {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n) (h6 : n ≠ 6)
    (h : ¬ (n % p = 2 ∨ n % p = 4 % p)) : IsLocallyOTwoBalancedWrtP p 1 ↥(alternatingGroup (Fin n)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  let Φ : Perm (Fin n) ≃* MulAut ↥(alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 h6)
  intro A hA D hD H hH hDH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, pow_one] at hDc
    exact hp.one_lt.ne hDc
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hdo : orderOf d = p := orderOf_eq_prime (hDel.2 d hdD) hd1'
  have hDeq : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdD)
      (by rw [Nat.card_zpowers, hdo, hDc, pow_one])).symm
  rw [hDeq, localDeltaTwoIn_zpowers hp hdo]
  set σ : Perm (Fin n) := Φ.symm d with hσ
  have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, ← hdo, pow_orderOf_eq_one, map_one]
  set H' : Subgroup (Perm (Fin n)) := H.map Φ.symm.toMonoidHom with hH'
  have hAH' : alternatingGroup (Fin n) ≤ H' := by
    intro a ha
    refine ⟨Φ a, hH ⟨⟨a, ha⟩, ?_⟩, by simp⟩
    ext x
    simp [Φ, MulAut.conjNormal_apply, MulAut.conj_apply]
  have hmod := AltFacts3.card_fix_modEq σ hσp
  rw [Nat.card_eq_fintype_card] at hmod
  have hfix2 : Fintype.card {i // σ i = i} ≠ 2 := by
    intro h2
    apply h
    left
    rw [h2] at hmod
    rw [← hmod]
    exact Nat.mod_eq_of_lt (by omega)
  have hfix4 : Fintype.card {i // σ i = i} ≠ 4 := by
    intro h4
    apply h
    right
    rw [h4] at hmod
    exact hmod.symm
  have h0 := pCoreOf_eq_bot_of_card_fix hp hp2 hσp hAH' hfix2 hfix4
  have hHH : H'.map Φ.toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨Φ.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hmap : (H' ⊓ Subgroup.centralizer ({σ} : Set (Perm (Fin n)))).map Φ.toMonoidHom =
      H ⊓ Subgroup.centralizer ({d} : Set (MulAut ↥(alternatingGroup (Fin n)))) := by
    rw [map_inf_centralizer Φ.toMonoidHom Φ.injective, hHH]
    simp [hσ]
  rw [← hmap, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 Φ, h0, Subgroup.map_bot]

end AltN

section AltSix

open Equiv Equiv.Perm
open CFSG.HardMathSupport.Solomon.Proving.AutSixBalance (card_mulAut_alt6 card_dvd_nine_of_isPGroup
  card_F06_map_conj)
open CFSG.RankThree.PartTwo.Sec4.Item434AltPerm (F06 isElemAbelian_F06)

theorem balanced_alt6_of_not_dvd {p : ℕ} (hp1440 : ¬ p ∣ 1440) :
    IsLocallyOTwoBalancedWrtP p 1 ↥(alternatingGroup (Fin 6)) := by
  intro A hA D hD H hH hDH
  exfalso
  apply hp1440
  have h1 := Subgroup.card_subgroup_dvd_card D
  rwa [hD.2.2, pow_one, card_mulAut_alt6] at h1

theorem balanced_alt6_three : IsLocallyOTwoBalancedWrtP 3 1 ↥(alternatingGroup (Fin 6)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Sylow 3 (MulAut ↥(alternatingGroup (Fin 6)))) :=
    Finite.of_injective (fun P : Sylow 3 (MulAut ↥(alternatingGroup (Fin 6))) =>
      (P : Set (MulAut ↥(alternatingGroup (Fin 6))))) (fun P Q h => SetLike.coe_injective h)
  intro A hA D hD H hH hDH
  obtain ⟨hDA, hDel, hDc⟩ := hD
  have hDne : D ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot, pow_one] at hDc
    exact absurd hDc (by norm_num)
  obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
  have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
  have hdo : orderOf d = 3 := orderOf_eq_prime (hDel.2 d hdD) hd1'
  have hDeq : D = Subgroup.zpowers d :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdD)
      (by rw [Nat.card_zpowers, hdo, hDc, pow_one])).symm
  rw [hDeq, localDeltaTwoIn_zpowers Nat.prime_three hdo]
  set H0 : Subgroup (MulAut ↥(alternatingGroup (Fin 6))) :=
    F06.map (MulAut.conj : ↥(alternatingGroup (Fin 6)) →* MulAut ↥(alternatingGroup (Fin 6))) with hH0
  have hH0c : Nat.card H0 = 9 := card_F06_map_conj
  have hH0p : IsPGroup 3 ↥H0 := IsPGroup.of_card (n := 2) (by rw [hH0c]; norm_num)
  obtain ⟨S0, hH0S0⟩ := hH0p.exists_le_sylow
  have hS0eq : (S0 : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))) = H0 := by
    refine (Subgroup.eq_of_le_of_card_ge hH0S0 ?_).symm
    rw [hH0c]
    exact Nat.le_of_dvd (by norm_num) (card_dvd_nine_of_isPGroup S0.isPGroup')
  have hH0e : ∀ h ∈ H0, h ^ 3 = 1 ∧ h ∈ innerAut ↥(alternatingGroup (Fin 6)) := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨by rw [← map_pow, isElemAbelian_F06.2 f hf, map_one], ⟨f, rfl⟩⟩
  have hdp : IsPGroup 3 ↥(Subgroup.zpowers d) :=
    l119_isPGroup_zpowers (p := 3) (x := d) (by rw [← hdo]; exact pow_orderOf_eq_one d)
  obtain ⟨Q, hdQ⟩ := hdp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut ↥(alternatingGroup (Fin 6))) S0 Q
  have hQmem : ∀ q ∈ (Q : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))), ∃ h ∈ H0, q = g * h * g⁻¹ := by
    intro q hq
    have hq' : q ∈ ((g • S0 : Sylow 3 (MulAut ↥(alternatingGroup (Fin 6)))) :
        Set (MulAut ↥(alternatingGroup (Fin 6)))) := by
      rw [hg]; exact hq
    rw [Sylow.coe_smul] at hq'
    obtain ⟨h, hh, hqh⟩ := Set.mem_smul_set.1 hq'
    refine ⟨h, hS0eq ▸ hh, ?_⟩
    rw [← hqh]
    simp [MulAut.smul_def, MulAut.conj_apply]
  have hQc : Nat.card (Q : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))) = 9 := by
    rw [← hH0c, ← hS0eq]
    exact Nat.card_congr (Sylow.equiv Q S0).toEquiv
  have hInn : (innerAut ↥(alternatingGroup (Fin 6))).Normal := Lemma123.innerAut_normal _
  have hQI : (Q : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))) ≤ innerAut ↥(alternatingGroup (Fin 6)) := by
    intro q hq
    obtain ⟨h, hh, rfl⟩ := hQmem q hq
    exact hInn.conj_mem _ (hH0e h hh).2 g
  have hQel : IsElemAbelian 3 (Q : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))) := by
    refine ⟨⟨⟨fun a b => IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hQc]; norm_num) a b⟩⟩,
      fun q hq => ?_⟩
    obtain ⟨h, hh, rfl⟩ := hQmem q hq
    rw [conj_pow, (hH0e h hh).1, mul_one, mul_inv_cancel]
  have hQC : (Q : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))) ≤ Subgroup.centralizer ({d} : Set _) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hQel.1.is_comm.comm ⟨q, hq⟩ ⟨d, hdQ (Subgroup.mem_zpowers d)⟩)
  set T : Subgroup (MulAut ↥(alternatingGroup (Fin 6))) :=
    pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set _)) with hT
  have hT2 : IsPGroup 2 ↥T := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hTc : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hT2
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hQT : (Q : Subgroup (MulAut ↥(alternatingGroup (Fin 6)))) ≤ Subgroup.normalizer (T : Set _) :=
    (le_inf (hQI.trans hH) hQC).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  exact CFSG.HardMathSupport.Solomon.Coordinator.i271AutBalanceAltSix_holds _ hQel (by rw [hQc]; norm_num) T
    hTc hQT

theorem not_balanced_alt6_five : ¬ IsLocallyOTwoBalancedWrtP 5 1 ↥(alternatingGroup (Fin 6)) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set G6 := MulAut ↥(alternatingGroup (Fin 6)) with hG6
  set x : Perm (Fin 6) := c[(0 : Fin 6), 1, 2, 3, 4] with hx
  have hxA : x ∈ alternatingGroup (Fin 6) := by rw [Perm.mem_alternatingGroup]; decide
  set Φ : Perm (Fin 6) →* G6 := MulAut.conjNormal (H := alternatingGroup (Fin 6)) with hΦ
  have hΦi : Function.Injective Φ :=
    CFSG.GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup 6 (by norm_num)
  set d : G6 := MulAut.conj (⟨x, hxA⟩ : ↥(alternatingGroup (Fin 6))) with hd
  have hdΦ : d = Φ x := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    rw [hΦ, MulAut.conjNormal_apply, hd, MulAut.conj_apply]
    rfl
  have hx5 : x ^ 5 = 1 := by decide
  have hx1 : x ≠ 1 := by decide
  have hdo : orderOf d = 5 := by
    rw [hdΦ, orderOf_injective Φ hΦi]
    exact orderOf_eq_prime hx5 hx1
  set C : Subgroup G6 := Subgroup.centralizer ({d} : Set G6) with hC
  have hG : Nat.card G6 = 1440 := card_mulAut_alt6
  have hidx1 : C.index ≤ 144 := by
    rw [hC, Subgroup.index_centralizer_eq_ncard]
    set X5 : Set ↥(alternatingGroup (Fin 6)) := {y | y ^ 5 = 1 ∧ y ≠ 1} with hX5
    have hsub : conjugatesOf d ⊆ (fun y => MulAut.conj y) '' X5 := by
      intro h hh
      obtain ⟨α, rfl⟩ := isConj_iff.1 hh
      refine ⟨α ⟨x, hxA⟩, ⟨?_, ?_⟩, ?_⟩
      · rw [← map_pow]
        have : (⟨x, hxA⟩ : ↥(alternatingGroup (Fin 6))) ^ 5 = 1 := Subtype.ext hx5
        rw [this, map_one]
      · intro h1
        apply hx1
        have : (⟨x, hxA⟩ : ↥(alternatingGroup (Fin 6))) = 1 := α.injective (h1.trans (map_one α).symm)
        exact congrArg Subtype.val this
      · exact (mul_conj_mul_inv α _).symm
    have hX5c : X5.ncard ≤ 144 := by
      have ht : ({g : Perm (Fin 6) | g ^ 5 = 1 ∧ g ≠ 1} : Set (Perm (Fin 6))) =
          ↑(Finset.univ.filter (fun g : Perm (Fin 6) => g ^ 5 = 1 ∧ g ≠ 1)) := by
        ext g; simp
      have hcount : (Finset.univ.filter (fun g : Perm (Fin 6) => g ^ 5 = 1 ∧ g ≠ 1)).card = 144 := by
        decide +kernel
      calc X5.ncard ≤ ({g : Perm (Fin 6) | g ^ 5 = 1 ∧ g ≠ 1} : Set (Perm (Fin 6))).ncard := by
            refine Set.ncard_le_ncard_of_injOn (fun y : ↥(alternatingGroup (Fin 6)) => (y : Perm (Fin 6)))
              (fun y hy => ⟨by simpa using congrArg Subtype.val hy.1, fun h => hy.2 (Subtype.ext h)⟩)
              (fun a _ b _ h => Subtype.ext h)
        _ = 144 := by rw [ht, Set.ncard_coe_finset, hcount]
    calc (conjugatesOf d).ncard ≤ ((fun y => MulAut.conj y) '' X5).ncard :=
          Set.ncard_le_ncard hsub
      _ ≤ X5.ncard := Set.ncard_image_le
      _ ≤ 144 := hX5c
  have hCR : C ⊓ Φ.range = (Subgroup.centralizer ({x} : Set (Perm (Fin 6)))).map Φ := by
    have h1 := map_inf_centralizer Φ hΦi ⊤ x
    rw [top_inf_eq, ← MonoidHom.range_eq_map, ← hdΦ] at h1
    rw [h1, inf_comm]
  have hCRc : Nat.card ↥(C ⊓ Φ.range) = 5 := by
    rw [hCR, Subgroup.card_map_of_injective hΦi, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have h1 : (Finset.univ.filter (fun g : Perm (Fin 6) => g ∈ Subgroup.centralizer ({x} : Set (Perm (Fin 6))))) =
        Finset.univ.filter (fun g : Perm (Fin 6) => g * x = x * g) := by
      ext g; simp [Subgroup.mem_centralizer_singleton_iff]
    rw [h1, hx]
    decide +kernel
  have hRc : Nat.card ↥Φ.range = 720 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦi).toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have hRi : Φ.range.index = 2 := by
    have h1 := Subgroup.card_mul_index Φ.range
    rw [hRc, hG] at h1
    omega
  have hCRi : (C ⊓ Φ.range).index = 288 := by
    have h1 := Subgroup.card_mul_index (C ⊓ Φ.range)
    rw [hCRc, hG] at h1
    omega
  have hidx2 : 144 ≤ C.index := by
    have h1 := Subgroup.index_inf_le (H := C) (K := Φ.range)
    rw [hCRi, hRi] at h1
    omega
  have hCc : Nat.card C = 10 := by
    have h1 := Subgroup.card_mul_index C
    rw [hG, show C.index = 144 by omega] at h1
    omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 2 (by rw [hCc]; norm_num)
  have ht' : orderOf (t : G6) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
  have hdC : d ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have htd : Commute (t : G6) d := Subgroup.mem_centralizer_singleton_iff.1 t.2
  have hdt : orderOf (d * (t : G6)) = 10 := by
    rw [htd.symm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hdo, ht']; norm_num), hdo, ht']
  have hCz : C = Subgroup.zpowers (d * (t : G6)) := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 (C.mul_mem hdC t.2)) ?_).symm
    rw [hCc, Nat.card_zpowers, hdt]
  have htz : (t : G6) ∈ Subgroup.zpowers (d * (t : G6)) := hCz ▸ t.2
  set V : Subgroup G6 := Subgroup.zpowers (t : G6) with hV
  have hV2 : IsPGroup 2 ↥V :=
    l119_isPGroup_zpowers (p := 2) (x := (t : G6)) (by rw [← ht']; exact pow_orderOf_eq_one _)
  have hVne : V ≠ ⊥ := by
    intro h
    have h1 : (t : G6) ∈ V := Subgroup.mem_zpowers _
    rw [h, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at ht'
    exact absurd ht' (by norm_num)
  have hVC : V ≤ ⊤ ⊓ C := le_inf le_top (Subgroup.zpowers_le.2 t.2)
  have hcommC : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    rw [hCz] at ha hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact zpow_mul_comm _ i j
  have hnorm : ⊤ ⊓ C ≤ Subgroup.normalizer (V : Set G6) := by
    rw [top_inf_eq]
    refine le_normalizer_of_conj fun c hc v hv => ?_
    have hvC : v ∈ C := Subgroup.zpowers_le.2 t.2 hv
    rw [hcommC c hc v hvC, mul_inv_cancel_right]
    exact hv
  refine not_balanced_of_core (by norm_num) hdo (H := ⊤) le_top (Subgroup.mem_top d) ?_
  intro hbot
  apply hVne
  have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVC hnorm hV2
  rw [hbot] at h1
  exact le_bot_iff.1 h1

end AltSix

theorem input19_17_1_holds :
    ∀ (p n : ℕ), p.Prime → p ≠ 2 → 5 ≤ n →
      (¬ IsLocallyOTwoBalancedWrtP p 1 ↥(alternatingGroup (Fin n)) ↔
        (n % p = 2 ∨ n % p = 4 % p ∨ (p = 5 ∧ n = 6))) := by
  intro p n hp hp2 hn5
  by_cases h6 : n = 6
  · subst h6
    by_cases hp5 : p = 5
    · subst hp5
      exact ⟨fun _ => Or.inr (Or.inr ⟨rfl, rfl⟩), fun _ => not_balanced_alt6_five⟩
    have hR : ¬ (6 % p = 2 ∨ 6 % p = 4 % p ∨ (p = 5 ∧ 6 = 6)) := by
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      rintro (h | h | ⟨h, -⟩)
      · have h1 : (6 - 2) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq (by rw [h, Nat.mod_eq_of_lt (by omega)])
        have h2 : p ∣ 2 ^ 2 := Nat.dvd_of_mod_eq_zero h1
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
      · have h1 : (6 - 4) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
        have h2 : p ∣ 2 := Nat.dvd_of_mod_eq_zero h1
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
      · exact hp5 h
    refine ⟨fun h => absurd ?_ h, fun h => absurd h hR⟩
    by_cases hp3 : p = 3
    · subst hp3
      exact balanced_alt6_three
    · refine balanced_alt6_of_not_dvd fun h => ?_
      have h1440 : (1440 : ℕ) = 2 ^ 5 * 3 ^ 2 * 5 := by norm_num
      rw [h1440] at h
      rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
      · rcases (Nat.Prime.dvd_mul hp).1 h' with h'' | h''
        · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h''))
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h''))
      · exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h')
  · constructor
    · intro hnb
      by_contra hR
      exact hnb (balanced_alt_of_not_mod hp hp2 hn5 h6 fun h => hR (h.elim Or.inl (Or.inr ∘ Or.inl)))
    · rintro (h | h | ⟨-, h⟩)
      · exact not_balanced_alt_of_mod hp hp2 hn5 (Or.inl h)
      · exact not_balanced_alt_of_mod hp hp2 hn5 (Or.inr h)
      · exact absurd h h6

section Chevp

open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple onLie ambiguousChev)

theorem pCoreOf_two_le_glaPPrimeCoreOf {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (X : Subgroup M) : pCoreOf 2 X ≤ GLAPPrimeCoreOf p X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  refine sec11_le_glaPPrimeCoreOf (CFSG.LieType.BorelTits.pCoreOf_le 2 X) ?_ ?_
  · intro h hh n hn
    exact (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hh) n).1 hn
  · exact (Nat.Prime.coprime_iff_not_dvd hp).2
      (Lemma123.not_dvd_card_of_isPGroup_two hp hp2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X))

@[expose] def Input19_6_4Outer : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → IsChevSimple p S →
    ∀ x : MulAut S, orderOf x = p → x ∉ innerAut S → ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
      x ∈ Subgroup.normalizer (H : Set (MulAut S)) →
        pCoreOf 2 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) ≠ ⊥ → p = 3 ∧ IsLTwoTwentySeven S

@[expose] def Input19_6_4Amb : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    ∀ idx : TauCeti.ValidLieTypeIndex, Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group) →
      ambiguousChev p (TauCeti.CFSGIndex.lie idx) → ∀ x ∈ innerAut S, orderOf x = p →
        ∀ H : Subgroup (MulAut S), innerAut S ≤ H →
          pCoreOf 2 (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) = ⊥

theorem input19_6_4_of (hCore : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hOut : Input19_6_4Outer) (hAmb : Input19_6_4Amb) : Lemma123.Input19_6_4 := by
  intro p hp hp2 Y _ _ hq hO hchev B hB hnb
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a := Prop1116Design.not_isCommutative_barQuot Y hq
  set f : MulAut Y →* MulAut (Y ⧸ Subgroup.center Y) := Lemma123.autQ Y with hf
  have hfi : Function.Injective f := Lemma123.autQ_injective hq.1
  have hBel : IsElemAbelian p (B.map f) := CFSG.SectionRank.isElemAbelian_map hB f
  have hnb' : ¬ IsLocallyOTwoBalanced p 1 (B.map f) := fun h =>
    hnb (isLocallyOTwoBalanced_of_map f hfi (innerAut_le_map_autQ Y) h)
  have hnS : ¬ IsLocallyOTwoBalancedWrtP p 1 (Y ⧸ Subgroup.center Y) := fun h => hnb' (h _ hBel)
  obtain ⟨d, hdB, hdo, H, hH, hdH, hne⟩ : ∃ d ∈ B.map f, orderOf d = p ∧
      ∃ H : Subgroup (MulAut (Y ⧸ Subgroup.center Y)), innerAut (Y ⧸ Subgroup.center Y) ≤ H ∧
        d ∈ Subgroup.normalizer (H : Set (MulAut (Y ⧸ Subgroup.center Y))) ∧
        pCoreOf 2 (H ⊓ Subgroup.centralizer ({d} : Set (MulAut (Y ⧸ Subgroup.center Y)))) ≠ ⊥ := by
    by_contra hcon
    apply hnb'
    intro D hD H hH hDH
    obtain ⟨hDA, hDel, hDc⟩ := hD
    have hDne : D ≠ ⊥ := by
      intro h0
      rw [h0, Subgroup.card_bot, pow_one] at hDc
      exact hp.one_lt.ne hDc
    obtain ⟨⟨d, hdD⟩, hd1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hDne
    have hd1' : d ≠ 1 := fun e => hd1 (Subtype.ext e)
    have hdo : orderOf d = p := orderOf_eq_prime (hDel.2 d hdD) hd1'
    have hDeq : D = Subgroup.zpowers d :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hdD)
        (by rw [Nat.card_zpowers, hdo, hDc, pow_one])).symm
    rw [hDeq, localDeltaTwoIn_zpowers hp hdo]
    by_contra hne
    exact hcon ⟨d, hDA hdD, hdo, H, hH, hDH hdD, hne⟩
  have hBI : d ∉ innerAut (Y ⧸ Subgroup.center Y) → ¬ B ≤ innerAut Y := by
    intro hdI hBI
    apply hdI
    obtain ⟨b, hb, rfl⟩ := hdB
    obtain ⟨y, rfl⟩ := hBI hb
    exact ⟨(y : Y ⧸ Subgroup.center Y), (Lemma123.autQ_conj y).symm⟩
  rcases hchev with ⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie idx =>
      by_cases hdI : d ∈ innerAut (Y ⧸ Subgroup.center Y)
      · exfalso
        have h0 := hCore _ inferInstance hnab idx ⟨e⟩ p hp hp2 hi d hdI hdo H hH
        exact hne (le_bot_iff.1 ((pCoreOf_two_le_glaPPrimeCoreOf hp hp2 _).trans h0.le))
      · obtain ⟨hp3, hL⟩ := hOut p hp hp2 _ inferInstance (Or.inl ⟨_, hi, ⟨e⟩⟩) d hdo hdI H hH hdH hne
        exact ⟨hp3, hL, hBI hdI⟩
    | cyclic _ _ => exact absurd hi (by simp [onLie])
    | alternating _ _ => exact absurd hi (by simp [onLie])
    | sporadic _ => exact absurd hi (by simp [onLie])
  · cases i with
    | alternating n hn =>
      exfalso
      apply hnS
      refine (isLocallyOTwoBalancedWrtP_congr e).2 ?_
      simp only [ambiguousChev] at hi
      rcases hi with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · obtain rfl : p = 5 := h.resolve_left hp2
        exact balanced_alt_of_not_mod hp hp2 le_rfl (by norm_num) (by norm_num)
      · obtain rfl : p = 3 := h.resolve_left hp2
        exact balanced_alt6_three
      · exact absurd h hp2
    | lie idx =>
      by_cases hdI : d ∈ innerAut (Y ⧸ Subgroup.center Y)
      · exact absurd (hAmb p hp hp2 _ inferInstance idx ⟨e⟩ hi d hdI hdo H hH) hne
      · obtain ⟨hp3, hL⟩ := hOut p hp hp2 _ inferInstance (Or.inr ⟨_, hi, ⟨e⟩⟩) d hdo hdI H hH hdH hne
        exact ⟨hp3, hL, hBI hdI⟩
    | cyclic _ _ => exact absurd hi (by simp [ambiguousChev])
    | sporadic _ => exact absurd hi (by simp [ambiguousChev])

end Chevp

section Simple

@[expose] def Input19_17_2S : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (s : TauCeti.SporadicName) (S : Type) [Group S] [Finite S],
    IsSporType s S → (¬ IsLocallyOTwoBalancedWrtP p 2 S ∨ ¬ IsWeaklyLocallyOTwoBalancedWrtP p 1 S) →
      (p = 5 ∧ s = TauCeti.SporadicName.Fi22) ∨
        (p = 3 ∧ (s = TauCeti.SporadicName.M12 ∨ s = TauCeti.SporadicName.M22 ∨ s = TauCeti.SporadicName.J2))

theorem input19_17_2_of (h : Input19_17_2S) : Lemma123.Input19_17_2 := by
  intro p hp hp2 s Y _ _ hq hO hs hnb
  refine h p hp hp2 s (Y ⧸ Subgroup.center Y) hs ?_
  rcases hnb with h1 | h1
  · exact Or.inl fun h2 => h1 (isLocallyOTwoBalancedWrtP_of_quot hq.1 h2)
  · exact Or.inr fun h2 => h1 (isWeaklyLocallyOTwoBalancedWrtP_of_quot hq.1 h2)

@[expose] def Input19_18S : Prop :=
  ∀ (p : ℕ), p.Prime → 3 < p → ∀ (S : Type) [Group S] [Finite S],
    ((IsSimpleGroup S ∧ Prop1116Design.IsLieOverField 3 S) ∨ (p = 13 ∧ IsLpType 3 (3 ^ 13) S)) →
      IsWeaklyLocallyOTwoBalancedWrtP p 1 S

theorem center_quot_eq_bot {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  rcases (Subgroup.center (Y ⧸ Subgroup.center Y)).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := Prop1116Design.not_isCommutative_barQuot Y hq
    apply hab
    have ha : a ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by rw [h]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem input19_18_of (h : Input19_18S) : Lemma123.Input19_18 := by
  intro Y _ _ hq _ hform
  have hp : Nat.Prime 13 := by norm_num
  rcases hform with h1 | h1
  · refine isWeaklyLocallyOTwoBalancedWrtP_of_quot hq.1 (h 13 hp (by norm_num) _ (Or.inl ⟨hq.2, ?_⟩))
    obtain ⟨idx, ⟨e⟩, hidx⟩ := h1
    exact ⟨idx, ⟨(Prop1116Design.mulEquivQuotCenterOfEqBot (center_quot_eq_bot hq)).symm.trans e⟩, hidx⟩
  · exact h 13 hp (by norm_num) Y (Or.inr ⟨rfl, h1⟩)

end Simple

section Alt

theorem input19_17_1c_of (hSchur : Lemma123.InputSchurAlt') :
    Lemma123.Input19_17_1c := by
  have h1917 := input19_17_1_holds
  intro p n hp hp2 hn5 Y _ _ hq hO hAlt
  obtain ⟨θ⟩ := hAlt
  rcases hSchur p n hp hp2 Y hq hO ⟨θ⟩ with hZ | ⟨rfl, hn67⟩
  · let e : Y ≃* ↥(alternatingGroup (Fin n)) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans θ
    exact (not_congr (isLocallyOTwoBalancedWrtP_congr e)).trans (h1917 p n hp hp2 hn5)
  · rcases hn67 with rfl | rfl
    · have hA6 : IsLocallyOTwoBalancedWrtP 3 1 ↥(alternatingGroup (Fin 6)) := by
        by_contra h
        have := (h1917 3 6 Nat.prime_three (by norm_num) (by norm_num)).1 h
        norm_num at this
      have hY := isLocallyOTwoBalancedWrtP_of_quot hq.1 ((isLocallyOTwoBalancedWrtP_congr θ).2 hA6)
      constructor
      · intro h; exact absurd hY h
      · intro h; norm_num at h
    · constructor
      · intro _; norm_num
      · intro _
        exact not_balanced_of_four Nat.prime_three θ (σ := c[(0 : Fin 7), 1, 2])
          (by rw [Equiv.Perm.mem_alternatingGroup]; decide) (by decide) (by decide) (by decide)

theorem input19_17_1c_of_schur (hSchur : Lemma123.InputSchurAlt') : Lemma123.Input19_17_1c :=
  input19_17_1c_of hSchur

theorem input19_17_1c_holds : Lemma123.Input19_17_1c :=
  input19_17_1c_of_schur SchurFacts.inputSchurAlt'_holds

end Alt

theorem lemma123_of_inputs_i19
    (h112 : Prop112Statement) (h115 : Prop115Statement)
    (h117 : Prop117_cex_falseStatement) (h122 : Lemma122_i_iiStatement) (h1116 : Prop1116StrongStatement)
    (hI185 : Sec12a.Input18_5) (hI191 : Lemma136c.Input19_1_O2)
    (hI22 : Input22_3_2) (hDiag : Lemma123.InputDiagBalance)
    (hDefCore : CFSG.HardMathSupport.Timmesfeld.Coordinator.DefCharInnerCoreFree)
    (hOut : Input19_6_4Outer) (hAmb : Input19_6_4Amb) (hI2317 : Lemma123.Input23_17)
    (hI234 : Lemma123.Input23_4) (hSchurAlt : Lemma123.InputSchurAlt')
    (hL27 : Prop1116.InputNotL27Pi)
    (hI1917s : Input19_17_2S) (hI2324 : Lemma123.Input23_24) (hSchurFi : Lemma123.InputSchurFi22)
    (hCore : CFSG.LieType.ChevTwo.Chev2CoreCent) (hKD : CFSG.LieType.ChevTwo.Chev2KDOut)
    (hI1916 : Lemma123.Input19_16_two)
    (hI7L : Input7_L34)
    (hI197 : Lemma123.Input19_7_3) (hI1918 : Input19_18S) (hI272 : Lemma123.Input27_2) :
    Lemma123Statement :=
  lemma123_of_inputs h112 h115 h117 h122 h1116 hI185 hI191 input19_1_O2_img_holds hI22 hDiag
    (input19_6_4_of hDefCore hOut hAmb) hI2317 (input19_17_1c_of_schur hSchurAlt) hI234 hSchurAlt hL27
    (input19_17_2_of hI1917s) hI2324 hSchurFi hCore hKD hI1916 hI7L hI197 (input19_18_of hI1918) hI272

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs123a
