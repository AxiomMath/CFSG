module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGold
public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs
import CFSG.LocalAnalysis.ComponentClassification.AS81QbarComp
import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma21Basic
import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarType

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.Goldschmidt CFSG.LocalCores
open CFSG.ComponentClassification.AS81.Qbar (conjAutOn conjAutOn_apply quotCenterAutHom
  quotCenterAutHom_mk compPermHom compPermHom_apply four_pow_card_componentIndex_le
  exists_mem_conj_ne isSylowOf_inf_component le_normalizer_of_inducesOmega1 sameOn_of_mk_eq
  conjAutOn_eq_of_sameOn apply_mem_of_compPerm)
open scoped commutatorElement

namespace RuGold

theorem eq_one_of_odd_of_fix_sylow {L : Type} [Group L] [Finite L]
    (hL : fusionIsBenderGroup L) (R : Sylow 2 L) (α : MulAut L)
    (hα : ∀ r ∈ (R : Subgroup L), α r = r) (hodd : Odd (orderOf α)) : α = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := AschbacherToolkit.BenderExt.benderData_of_isBenderGroup hL
  obtain ⟨q, k, -, hB⟩ := hD.borel
  have : IsSimpleGroup L := hD.simple
  have hSE := (hB R).1
  have hcard := GoldType.card_sylow_of_bender hL R
  have hαn : ∀ n : ℕ, ∀ s ∈ (R : Subgroup L), (α ^ n) s = s := by
    intro n
    induction n with
    | zero => intro s _; rfl
    | succ n ih => intro s hs; rw [pow_succ, MulAut.mul_apply, hα s hs, ih s hs]
  have hαR : ∀ n : ℕ, (α ^ n) • R = R := fun n =>
    AschbacherToolkit.Bender.Omega.smul_eq_of_mapsTo fun s hs => by rw [hαn n s hs]; exact hs
  have h2 : 1 < Nat.card (Sylow 2 L) := by
    rw [hcard]
    have := Nat.card_pos (α := (R : Subgroup L))
    omega
  have : Nontrivial (Sylow 2 L) := Finite.one_lt_card_iff_nontrivial.mp h2
  obtain ⟨S₀, h₀⟩ := exists_ne R
  have hαS₀ : α • S₀ ≠ R := by
    intro h
    apply h₀
    calc S₀ = α⁻¹ • (α • S₀) := (inv_smul_smul α S₀).symm
      _ = α⁻¹ • (α • R) := by rw [h, ← pow_one α, hαR 1]
      _ = R := inv_smul_smul α R
  obtain ⟨r, hr, hrS⟩ := AschbacherToolkit.Bender.Omega.exists_smul_eq hSE hcard h₀ hαS₀
  have hpow : ∀ n : ℕ, (α ^ n) • S₀ = r ^ n • S₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_smul, ih, AschbacherToolkit.Bender.Omega.smul_conj_smul,
        hα _ (pow_mem hr n), ← hrS, smul_smul, ← pow_succ]
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp R.isPGroup'
  have hr1 : r ^ (2 ^ m) = 1 := by
    have h := pow_card_eq_one' (G := (R : Subgroup L)) (x := ⟨r, hr⟩)
    rw [hm] at h
    simpa using congrArg Subtype.val h
  have hfix : ∀ S : Sylow 2 L, (α ^ (2 ^ m)) • S = S := by
    intro S
    by_cases hS : S = R
    · rw [hS]
      exact hαR _
    · obtain ⟨r', hr', rfl⟩ := AschbacherToolkit.Bender.Omega.exists_smul_eq hSE hcard h₀ hS
      rw [AschbacherToolkit.Bender.Omega.smul_conj_smul, hαn _ r' hr', hpow, hr1, one_smul]
  have h1 := AschbacherToolkit.Bender.Omega.eq_one_of_forall_smul_eq R hSE.1 _ hfix
  have hdvd : orderOf α ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h1
  have hord : orderOf α = 1 :=
    (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)).eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.mp hord

theorem eq_one_of_perfect {K : Type*} [Group K] (hK : commutator K = ⊤) (α : MulAut K)
    (h : ∀ x : K, x⁻¹ * α x ∈ center K) : α = 1 := by
  have hfix : commutator K ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id K) := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    have ha := mem_center_iff.mp (h a)
    have hb := mem_center_iff.mp (h b)
    set za := a⁻¹ * α a with hza
    set zb := b⁻¹ * α b with hzb
    have hαa : α a = a * za := by rw [hza, mul_inv_cancel_left]
    have hαb : α b = b * zb := by rw [hzb, mul_inv_cancel_left]
    change α ⁅a, b⁆ = ⁅a, b⁆
    rw [map_commutatorElement, hαa, hαb, commutatorElement_def, commutatorElement_def]
    have hzz : za * zb * za⁻¹ = zb := by rw [← ha zb, mul_inv_cancel_right]
    calc a * za * (b * zb) * (a * za)⁻¹ * (b * zb)⁻¹
        = a * (za * b) * zb * za⁻¹ * a⁻¹ * zb⁻¹ * b⁻¹ := by group
      _ = a * (b * za) * zb * za⁻¹ * a⁻¹ * zb⁻¹ * b⁻¹ := by rw [← ha b]
      _ = a * b * (za * zb * za⁻¹) * a⁻¹ * zb⁻¹ * b⁻¹ := by group
      _ = a * b * zb * a⁻¹ * zb⁻¹ * b⁻¹ := by rw [hzz]
      _ = a * b * (zb * a⁻¹) * zb⁻¹ * b⁻¹ := by group
      _ = a * b * (a⁻¹ * zb) * zb⁻¹ * b⁻¹ := by rw [← hb a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  ext x
  have hx : x ∈ commutator K := by rw [hK]; exact mem_top x
  exact hfix hx

theorem mem_centralizer_of_bender {H : Type} [Group H] [Finite H]
    {K : Subgroup H} (hK : IsComponent K) (hB : fusionIsBenderGroup (K ⧸ center K))
    (P : Sylow 2 K) {w : H} (hwK : w ∈ normalizer (K : Set H))
    (hwP : ∀ p ∈ (P : Subgroup K), w * p = p * w) (hw : Odd (orderOf w)) :
    w ∈ centralizer (K : Set H) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwz : zpowers w ≤ normalizer (K : Set H) := zpowers_le.mpr hwK
  set α : MulAut K := conjAutOn K (zpowers w) hwz ⟨w, mem_zpowers w⟩ with hα
  have hαapp : ∀ x : K, (α x : H) = w * x * w⁻¹ := fun x => conjAutOn_apply _ _ hwz _ x
  set TL : Sylow 2 (K ⧸ center K) := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
    with hTL
  have hTLcoe : (TL : Subgroup (K ⧸ center K)) = (P : Subgroup K).map (QuotientGroup.mk' _) :=
    Sylow.coe_mapSurjective _ _
  have hfix : ∀ t ∈ (TL : Subgroup (K ⧸ center K)), quotCenterAutHom α t = t := by
    rw [hTLcoe]
    rintro _ ⟨p, hp, rfl⟩
    rw [QuotientGroup.mk'_apply, quotCenterAutHom_mk]
    congr 1
    apply Subtype.ext
    rw [hαapp, hwP p hp, mul_inv_cancel_right]
  have hodd : Odd (orderOf (quotCenterAutHom α)) := by
    have h1 : orderOf (quotCenterAutHom α) ∣ orderOf (⟨w, mem_zpowers w⟩ : zpowers w) :=
      orderOf_map_dvd (quotCenterAutHom.comp (conjAutOn K (zpowers w) hwz)) _
    rw [Subgroup.orderOf_mk] at h1
    exact hw.of_dvd_nat h1
  have h1 := eq_one_of_odd_of_fix_sylow hB TL _ hfix hodd
  have hcen : ∀ x : K, x⁻¹ * α x ∈ center K := by
    intro x
    have h := congrArg (fun φ : MulAut (K ⧸ center K) => φ (QuotientGroup.mk x)) h1
    simp only [quotCenterAutHom_mk, MulAut.one_apply] at h
    exact QuotientGroup.eq.mp h.symm
  have hα1 := eq_one_of_perfect hK.1.1.commutator_eq_top α hcen
  rw [mem_centralizer_iff]
  intro x hx
  have h2 := congrArg (fun φ : MulAut K => (φ ⟨x, hx⟩ : H)) hα1
  simp only [MulAut.one_apply] at h2
  rw [hαapp] at h2
  calc x * w = w * x * w⁻¹ * w := by rw [h2]
    _ = w * x := by group


section Sup

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem exists_pow_mem_of_mem_sup {P W : Subgroup H} (hP : IsPGroup 2 P)
    (hPW : P ≤ normalizer (W : Set H)) {c : H} (hc : c ∈ P ⊔ W) :
    ∃ m : ℕ, c ^ (2 ^ m) ∈ W := by
  obtain ⟨p, hp, w, hw, rfl⟩ := G37.mem_sup_of_le_normalizer hPW hc
  have key : ∀ n : ℕ, ∃ w' ∈ W, (p * w) ^ n = p ^ n * w' := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem W, by simp⟩
    | succ n ih =>
      obtain ⟨w', hw', he⟩ := ih
      refine ⟨p⁻¹ * w' * p * w, mul_mem ?_ hw, by rw [pow_succ, he, pow_succ]; group⟩
      have := (mem_normalizer_iff.mp (hPW (inv_mem hp)) w').mp hw'
      simpa using this
  obtain ⟨m, hm⟩ := hP ⟨p, hp⟩
  have hm' : p ^ (2 ^ m) = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨w', hw', he⟩ := key (2 ^ m)
  exact ⟨m, by rw [he, hm', one_mul]; exact hw'⟩

theorem le_of_perfect_of_le_sup {P W K : Subgroup H} (hP : IsPGroup 2 P)
    (hPW : P ≤ normalizer (W : Set H)) (hKW : K ≤ normalizer (W : Set H))
    (hK : commutator K = ⊤) (hKPW : K ≤ P ⊔ W) : K ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup K := W.subgroupOf K with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [hN, mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact (mem_normalizer_iff.mp (hKW k.2) n).mp hn
  have hQ : IsPGroup 2 (K ⧸ N) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨m, hm⟩ := exists_pow_mem_of_mem_sup hP hPW (hKPW k.2)
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hN, mem_subgroupOf]
    simpa using hm
  have : Group.IsNilpotent (K ⧸ N) := hQ.isNilpotent
  have hQtop : commutator (K ⧸ N) = ⊤ := by
    have hs := QuotientGroup.mk'_surjective N
    rw [commutator_def, ← map_top_of_surjective _ hs, ← map_commutator, ← commutator_def, hK,
      map_top_of_surjective _ hs]
  have hder : ∀ n, derivedSeries (K ⧸ N) n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, hQtop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := K ⧸ N)
  rw [hder] at hn
  intro k hk
  have h1 : (QuotientGroup.mk (⟨k, hk⟩ : K) : K ⧸ N) ∈ (⊥ : Subgroup (K ⧸ N)) :=
    hn ▸ mem_top _
  rwa [mem_bot, QuotientGroup.eq_one_iff, hN, mem_subgroupOf] at h1

end Sup

theorem not_le_sup_of_isComponent {H : Type} [Group H] [Finite H]
    (hO : goldschmidtOddCore H = ⊥) {P W K : Subgroup H} (hP : IsPGroup 2 P)
    (hW : Odd (Nat.card W)) (hPW : P ≤ normalizer (W : Set H))
    (hKW : K ≤ normalizer (W : Set H)) (hK : IsComponent K) : ¬ K ≤ P ⊔ W := by
  intro hKPW
  have hKle := le_of_perfect_of_le_sup hP hPW hKW hK.1.1.commutator_eq_top hKPW
  have hodd : Odd (Nat.card K) := hW.of_dvd_nat (card_dvd_of_le hKle)
  have hbot := G37.eq_bot_of_isSubnormal_of_odd hO hK.2 hodd
  have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
  obtain ⟨a, b, hab⟩ := exists_pair_ne (K ⧸ center K)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have hx : x = 1 := Subtype.ext ((eq_bot_iff_forall K).mp hbot x x.2)
  have hy : y = 1 := Subtype.ext ((eq_bot_iff_forall K).mp hbot y y.2)
  rw [hx, hy]

end RuGold

open RuGold

section Main

variable {H : Type} [Group H] [Finite H]

theorem normal_or_eq_bot_of_stronglyClosed
    (hO : goldschmidtOddCore H = ⊥) (S : Sylow 2 H)
    {X : Subgroup H} (hXS : X ≤ (S : Subgroup H)) (hXab : IsMulCommutative X)
    (hX : Nat.card X = 32) (hcl : fusionStronglyClosed (X : Set H) (S : Subgroup H))
    {f : H} (hfX : f ∈ X) (hf : orderOf f = 2) (hfZ : f ∈ center H)
    {g : H} (hgX : g ∈ normalizer (X : Set H)) (hg : Odd (orderOf g))
    (hirr : ∀ U : Subgroup H, zpowers f ≤ U → U ≤ X → g ∈ normalizer (U : Set H) →
      U = zpowers f ∨ U = X)
    (hD2 : ∀ K : Subgroup H, IsComponent K → ¬ K ≤ centralizer (X : Set H))
    {W : Subgroup H} (hW : Odd (Nat.card W))
    (hWS : W ≤ centralizer ((S : Subgroup H) : Set H)) :
    X.Normal ∨ W = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomp, hnorm⟩ := stronglyClosed_components_or_normal hO S hXS hXab hcl
  have hall : ∀ K : Subgroup H, IsComponent K → K ≤ normalClosure (X : Set H) := fun K hK =>
    (component_le_normalClosure_or_le_centralizer hK X).resolve_right fun h =>
      hD2 K hK (le_centralizer_iff.mp h)
  by_cases hex : ∃ K : Subgroup H, IsComponent K
  swap
  · exact Or.inl (hnorm fun K hK _ => hex ⟨K, hK⟩)
  right
  obtain ⟨K₀, hK₀⟩ := hex
  have htype : ∀ K : ComponentIndex H, goldschmidtSimpleType (K.1 ⧸ center K.1) := fun K =>
    (hcomp K.1 K.2 (hall K.1 K.2)).1
  have hind : ∀ K : ComponentIndex H, InducesOmega1 X K.1 (S : Subgroup H) := fun K =>
    (hcomp K.1 K.2 (hall K.1 K.2)).2.1
  have hcover : ∀ K : ComponentIndex H, ∀ a ∈ X, ∃ x ∈ X ⊓ K.1, ∀ y ∈ K.1,
      a⁻¹ * y * a = x⁻¹ * y * x := fun K => (hcomp K.1 K.2 (hall K.1 K.2)).2.2
  have hfc : ∀ y : H, ∀ z ∈ zpowers f, z * y = y * z := fun y z hz =>
    (mem_center_iff.mp (zpowers_le.mpr hfZ hz) y).symm
  have hne : ∀ K : ComponentIndex H, ∃ x ∈ X ⊓ K.1, ∃ y ∈ K.1, x⁻¹ * y * x ≠ y := by
    intro K
    obtain ⟨a, ha, y, hy, hay⟩ := exists_mem_conj_ne S K.2 (htype K) (hind K)
    obtain ⟨x, hx, hxa⟩ := hcover K a ha
    exact ⟨x, hx, y, hy, by rw [← hxa y hy]; exact hay⟩
  have hc4 := four_pow_card_componentIndex_le S htype hind hcover
  rw [hX] at hc4
  have hc2 : Nat.card (ComponentIndex H) ≤ 2 := by
    by_contra h
    push Not at h
    have h3 : 4 ^ 3 ≤ 4 ^ Nat.card (ComponentIndex H) := Nat.pow_le_pow_right (by norm_num) h
    omega
  have hgfix : ∀ K : ComponentIndex H, compPermHom (MulAut.conj g) K = K := by
    have h1 : orderOf (compPermHom (MulAut.conj g)) ∣ orderOf g :=
      orderOf_map_dvd (compPermHom.comp MulAut.conj) g
    have h2 : orderOf (compPermHom (MulAut.conj g)) ∣ 2 := by
      have h3 := orderOf_dvd_natCard (compPermHom (MulAut.conj g))
      rw [Nat.card_perm] at h3
      exact h3.trans (Nat.factorial_dvd_factorial hc2)
    have h4 : orderOf (compPermHom (MulAut.conj g)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at h1
        exact absurd (hg.of_dvd_nat h1) (by decide)
    intro K
    rw [orderOf_eq_one_iff.mp h4]
    rfl
  have hgN : ∀ K : ComponentIndex H, g ∈ normalizer (K.1 : Set H) := by
    intro K
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨k, hk, rfl⟩
    exact apply_mem_of_compPerm (hgfix K) hk
  have hc1 : 1 ≤ Nat.card (ComponentIndex H) := by
    have : Nonempty (ComponentIndex H) := ⟨⟨K₀, hK₀⟩⟩
    exact Nat.card_pos
  rcases Nat.lt_or_ge 1 (Nat.card (ComponentIndex H)) with hlt | hle
  ·
    exfalso
    have : Nontrivial (ComponentIndex H) := Finite.one_lt_card_iff_nontrivial.mp hlt
    obtain ⟨K₁, K₂, h12⟩ := exists_pair_ne (ComponentIndex H)
    set U : Subgroup H := (X ⊓ K₁.1) ⊔ zpowers f with hU
    have hUX : U ≤ X := sup_le inf_le_left (zpowers_le.mpr hfX)
    have hgU : g ∈ normalizer (U : Set H) := by
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      rw [hU, Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨x, ⟨hxX, hxK⟩, rfl⟩
        exact ⟨(mem_normalizer_iff.mp hgX x).mp hxX, (mem_normalizer_iff.mp (hgN K₁) x).mp hxK⟩
      · rintro _ ⟨z, hz, rfl⟩
        change g * z * g⁻¹ ∈ zpowers f
        rw [← hfc g z hz, mul_inv_cancel_right]
        exact hz
    rcases hirr U le_sup_right hUX hgU with h | h
    · obtain ⟨x, hx, y, hy, hxy⟩ := hne K₁
      have hxU : x ∈ U := mem_sup_left hx
      rw [h] at hxU
      exact hxy (by rw [mul_assoc, ← hfc y x hxU, inv_mul_cancel_left])
    · obtain ⟨a, ha, y, hy, hay⟩ := hne K₂
      have hUc : U ≤ centralizer (K₂.1 : Set H) := by
        refine sup_le ?_ ?_
        · intro x hx
          exact mem_centralizer_iff.mpr fun k hk =>
            (componentIndex_commute h12 x k (mem_inf.mp hx).2 hk).eq.symm
        · intro z hz
          exact mem_centralizer_iff.mpr fun k _ => (hfc k z hz).symm
      have haU : a ∈ U := by
        rw [h]
        exact (mem_inf.mp ha).1
      have hac := mem_centralizer_iff.mp (hUc haU) y hy
      exact hay (by rw [mul_assoc, hac, inv_mul_cancel_left])
  have huniq : ∀ K : Subgroup H, IsComponent K → K = K₀ := by
    intro K hK
    have : Subsingleton (ComponentIndex H) := Finite.card_le_one_iff_subsingleton.mp hle
    exact congrArg Subtype.val (Subsingleton.elim (⟨K, hK⟩ : ComponentIndex H) ⟨K₀, hK₀⟩)
  set K' : ComponentIndex H := ⟨K₀, hK₀⟩ with hK'
  set D : Subgroup H := X ⊓ centralizer (K₀ : Set H) with hD
  have hfD : zpowers f ≤ D := le_inf (zpowers_le.mpr hfX) fun z hz =>
    mem_centralizer_iff.mpr fun k _ => (hfc k z hz).symm
  have hgD : g ∈ normalizer (D : Set H) := by
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, ⟨hxX, hxC⟩, rfl⟩
    change g * x * g⁻¹ ∈ D
    refine ⟨(mem_normalizer_iff.mp hgX x).mp hxX, mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K₀ := (mem_normalizer_iff.mp (inv_mem (hgN K')) k).mp hk
    have h1 := mem_centralizer_iff.mp hxC _ hk'
    calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * k * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * k := by group
  rcases hirr D hfD inf_le_left hgD with hDf | hDX
  swap
  · exfalso
    obtain ⟨x, hx, y, hy, hxy⟩ := hne K'
    have hxD : x ∈ D := by
      rw [hDX]
      exact (mem_inf.mp hx).1
    exact hxy (by rw [mul_assoc, mem_centralizer_iff.mp hxD.2 y hy, inv_mul_cancel_left])
  have hXN := le_normalizer_of_inducesOmega1 S (hind K')
  set Φ := conjAutOn K₀ X hXN with hΦ
  have hker : Φ.ker = D.subgroupOf X := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    constructor
    · intro h
      refine ⟨a.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h1 := congrArg (fun e : MulAut K₀ => ((e ⟨y, hy⟩ : K₀) : H)) h
      simp only [hΦ, conjAutOn_apply, MulAut.one_apply] at h1
      calc y * a = (a : H) * y * (a : H)⁻¹ * a := by rw [h1]
        _ = a * y := by group
    · rintro ⟨-, h⟩
      refine MulEquiv.ext fun w => Subtype.ext ?_
      rw [hΦ, conjAutOn_apply]
      change (a : H) * w * (a : H)⁻¹ = w
      rw [← mem_centralizer_iff.mp h w w.2]
      group
  have hrange : Nat.card Φ.range = 16 := by
    have h := Subgroup.card_ker_mul_card_range Φ
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv, ← hD, hDf,
      Nat.card_zpowers, hf, hX] at h
    omega
  obtain ⟨P, hP⟩ := isSylowOf_inf_component S hK₀
  set TL : Sylow 2 (K₀ ⧸ center K₀) :=
    P.mapSurjective (QuotientGroup.mk'_surjective (center K₀)) with hTL
  have hTLcoe : (TL : Subgroup (K₀ ⧸ center K₀)) = (P : Subgroup K₀).map (QuotientGroup.mk' _) :=
    Sylow.coe_mapSurjective _ _
  have hlift : ∀ φ : Φ.range, ∃ a : X, Φ a = φ ∧ ∃ t : K₀, (t : H) ∈ (S : Subgroup H) ∧
      ∀ y ∈ K₀, (a : H)⁻¹ * y * a = (t : H)⁻¹ * y * t := by
    rintro ⟨_, a, rfl⟩
    obtain ⟨t, ⟨htS, htK⟩, -, hat⟩ := (hind K').1 a a.2
    exact ⟨a, rfl, ⟨t, htK⟩, htS, hat⟩
  choose a ha t htS hat using hlift
  have htTL : ∀ φ, (QuotientGroup.mk (t φ) : K₀ ⧸ center K₀) ∈
      (TL : Subgroup (K₀ ⧸ center K₀)) := by
    intro φ
    rw [hTLcoe]
    have h1 : ((t φ : K₀) : H) ∈ (P : Subgroup K₀).map K₀.subtype := by
      rw [hP]
      exact ⟨htS φ, (t φ).2⟩
    obtain ⟨p, hp, hpt⟩ := h1
    exact ⟨p, hp, by rw [QuotientGroup.mk'_apply]; congr 1; exact Subtype.ext hpt⟩
  have hFinj : Function.Injective
      (fun φ : Φ.range => (⟨_, htTL φ⟩ : (TL : Subgroup (K₀ ⧸ center K₀)))) := by
    intro φ φ' h
    have h1 : (QuotientGroup.mk (t φ) : K₀ ⧸ center K₀) = QuotientGroup.mk (t φ') :=
      congrArg Subtype.val h
    have h2 := sameOn_of_mk_eq h1
    have h3 : ∀ y ∈ K₀, ((a φ : X) : H)⁻¹ * y * (a φ) = ((a φ' : X) : H)⁻¹ * y * (a φ') :=
      fun y hy => (hat φ y hy).trans ((h2 y hy).trans (hat φ' y hy).symm)
    apply Subtype.ext
    rw [← ha φ, ← ha φ']
    exact conjAutOn_eq_of_sameOn hXN h3
  have h16 : 16 ≤ Nat.card (TL : Subgroup (K₀ ⧸ center K₀)) := by
    rw [← hrange]
    exact Nat.card_le_card_of_injective _ hFinj
  have : IsSimpleGroup (K₀ ⧸ center K₀) := hK₀.1.2.1
  have hB : fusionIsBenderGroup (K₀ ⧸ center K₀) := by
    rcases htype K' with ⟨f', hf', he⟩ | ⟨n, hn, he⟩ | ⟨f', hf', he⟩ |
        ⟨p, f', hp, hpo, hf', -, h8, ⟨e⟩⟩ | hRJ
    · exact Or.inl ⟨f', by omega, he⟩
    · exact Or.inr (Or.inr ⟨n, hn, he⟩)
    · exact Or.inr (Or.inl ⟨f', hf', he⟩)
    · exfalso
      have h4 := (GoldType.sylow_of_psl2_odd hpo hf' h8 e TL).1
      rw [h4] at h16
      omega
    · exfalso
      have h8' := (GoldType.sylow_of_ree_or_j1 hRJ TL).2.1
      rw [h8'] at h16
      omega
  have hWK : W ≤ centralizer (K₀ : Set H) := by
    intro w hw
    have hwN : w ∈ normalizer (K₀ : Set H) := by
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      exact (huniq _ (isComponent_map_mulEquiv (MulAut.conj w) hK₀)).le
    have hwP : ∀ p ∈ (P : Subgroup K₀), w * p = p * w := by
      intro p hp
      have hpS : (p : H) ∈ (S : Subgroup H) := by
        have h1 : (p : H) ∈ (P : Subgroup K₀).map K₀.subtype := ⟨p, hp, rfl⟩
        rw [hP] at h1
        exact h1.1
      exact (mem_centralizer_iff.mp (hWS hw) p hpS).symm
    exact mem_centralizer_of_bender hK₀ hB P hwN hwP
      (hW.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hw))
  have hF : GorensteinWalter.generalizedFittingSubgroupOf (⊤ : Subgroup H) ≤
      centralizer (W : Set H) := by
    unfold GorensteinWalter.generalizedFittingSubgroupOf
    refine sup_le ?_ ?_
    · change CFSG.fittingSubgroupOf (⊤ : Subgroup H) ≤ _
      rw [G37.fittingSubgroupOf_top_eq]
      have h2 : IsPGroup 2 (CFSG.fittingSubgroup H) := by
        have h3 := G37.isPGroup_fitting hO
        rwa [G37.fittingSubgroupOf_top_eq] at h3
      exact (h2.le_sylow_of_normal S).trans (le_centralizer_iff.mp hWS)
    · refine sSup_le fun E hE => ?_
      rw [huniq E ((CFSG.Walter.isComponent_iff_isComponentOf_top E).mpr hE)]
      exact le_centralizer_iff.mp hWK
  exact G37.eq_bot_of_le_centralizer_fstar hO hW (le_centralizer_iff.mp hF)

end Main

section Frame

variable {G : Type} [Group G] [Finite G]

open CFSG.ABGLocalTools in
theorem centralizer_le_normalizer_of_irreducible
    {W X P S₀ : Subgroup G} {f g : G}
    (hW : Odd (Nat.card W)) (hWS₀ : W ≤ centralizer (S₀ : Set G))
    (hO : AS76b.oddCoreIn (centralizer ({f} : Set G)) = ⊥)
    (hS₀ : IsSylowOf 2 S₀ (centralizer ({f} : Set G))) (hXS₀ : X ≤ S₀)
    (hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hX : Nat.card X = 32) (hfX : f ∈ X)
    (hf : orderOf f = 2)
    (hcl : ∀ x ∈ X, ∀ h ∈ centralizer ({f} : Set G), h⁻¹ * x * h ∈ S₀ → h⁻¹ * x * h ∈ X)
    (hgf : g ∈ centralizer ({f} : Set G)) (hgX : g ∈ normalizer (X : Set G))
    (hg : Odd (orderOf g))
    (hirr : ∀ U : Subgroup G, f ∈ U → U ≤ X → g ∈ normalizer (U : Set G) →
      U = zpowers f ∨ U = X)
    (hP : IsPGroup 2 P) (hCX : centralizer (X : Set G) = P ⊔ W)
    (hNX : normalizer (X : Set G) ≤ normalizer (W : Set G)) :
    centralizer ({f} : Set G) ≤ normalizer (W : Set G) := by
  classical
  set C := centralizer ({f} : Set G) with hC
  obtain ⟨Q, hQ⟩ := hS₀
  have hS₀C : S₀ ≤ C := hQ ▸ map_subtype_le _
  have hXC : X ≤ C := hXS₀.trans hS₀C
  have hfC : f ∈ C := hXC hfX
  have hWC : W ≤ C := fun w hw => mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (hWS₀ hw) f (hXS₀ hfX)).symm
  have hCXC : centralizer (X : Set G) ≤ C := centralizer_le (Set.singleton_subset_iff.mpr hfX)
  have hPC : P ≤ C := (le_sup_left.trans hCX.ge).trans hCXC
  have hCXN : centralizer (X : Set G) ≤ normalizer (W : Set G) :=
    (Subgroup.centralizer_le_normalizer (X : Set G)).trans hNX
  have hPW : P ≤ normalizer (W : Set G) := (le_sup_left.trans hCX.ge).trans hCXN
  set X' := X.subgroupOf C with hX'
  set W' := W.subgroupOf C with hW'
  set f' : C := ⟨f, hfC⟩ with hf'
  set g' : C := ⟨g, hgf⟩ with hg'
  have hO' : goldschmidtOddCore C = ⊥ := by
    have h1 : (CFSG.Assembly.oddCore C).map C.subtype = ⊥ := hO
    rw [map_eq_bot_iff_of_injective _ C.subtype_injective] at h1
    exact h1
  have hXS' : X' ≤ (Q : Subgroup C) := by
    intro x hx
    have h1 : (x : G) ∈ S₀ := hXS₀ (mem_subgroupOf.mp hx)
    rw [← hQ] at h1
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← Subtype.ext hyx]
  have hXab' : IsMulCommutative X' := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (hXab _ (mem_subgroupOf.mp a.2) _ (mem_subgroupOf.mp b.2)))⟩⟩
  have hX'32 : Nat.card X' = 32 := by
    rw [← hX]
    exact Nat.card_congr (subgroupOfEquivOfLe hXC).toEquiv
  have hcl' : fusionStronglyClosed (X' : Set C) (Q : Subgroup C) := by
    intro a ha h hh
    rw [SetLike.mem_coe, mem_subgroupOf]
    refine hcl _ (mem_subgroupOf.mp ha) _ h.2 ?_
    rw [← hQ]
    exact ⟨_, hh, rfl⟩
  have hfZ' : f' ∈ center C := mem_center_iff.mpr fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp c.2)
  have hgX' : g' ∈ normalizer (X' : Set C) := by
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mpr ((mem_normalizer_iff.mp hgX x).mp (mem_subgroupOf.mp hx))
  have hirr' : ∀ U : Subgroup C, zpowers f' ≤ U → U ≤ X' → g' ∈ normalizer (U : Set C) →
      U = zpowers f' ∨ U = X' := by
    intro U hfU hUX hgU
    have hgU' : g ∈ normalizer ((U.map C.subtype : Subgroup G) : Set G) := by
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨_, (mem_normalizer_iff.mp hgU u).mp hu, rfl⟩
    have hUX' : U.map C.subtype ≤ X := by
      rintro _ ⟨u, hu, rfl⟩
      exact mem_subgroupOf.mp (hUX hu)
    rcases hirr (U.map C.subtype) ⟨f', zpowers_le.mp hfU, rfl⟩ hUX' hgU' with h | h
    · left
      apply map_injective C.subtype_injective
      rw [h, MonoidHom.map_zpowers]
      rfl
    · right
      apply map_injective C.subtype_injective
      rw [h, hX', subgroupOf_map_subtype, inf_eq_left.mpr hXC]
  have hnorm : ∀ c : C, (c : G) ∈ normalizer (W : Set G) → c ∈ normalizer (W' : Set C) := by
    intro c hc
    rw [mem_normalizer_iff]
    intro x
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.mp hc x
  have hW'odd : Odd (Nat.card W') := by
    rwa [hW', Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv]
  have hD2' : ∀ K : Subgroup C, IsComponent K → ¬ K ≤ centralizer (X' : Set C) := by
    intro K hK hKX
    have hKCX : ∀ k ∈ K, (k : G) ∈ centralizer (X : Set G) := by
      intro k hk
      rw [mem_centralizer_iff]
      intro x hx
      exact congrArg Subtype.val
        (mem_centralizer_iff.mp (hKX hk) ⟨x, hXC hx⟩ (mem_subgroupOf.mpr hx))
    refine not_le_sup_of_isComponent hO' (hP.comap_of_injective C.subtype C.subtype_injective)
      hW'odd (fun p hp => hnorm p (hPW (mem_subgroupOf.mp hp)))
      (fun k hk => hnorm k (hCXN (hKCX k hk))) hK fun k hk => ?_
    change k ∈ P.subgroupOf C ⊔ W.subgroupOf C
    rw [← subgroupOf_sup hPC hWC, mem_subgroupOf, ← hCX]
    exact hKCX k hk
  have hWS' : W' ≤ centralizer ((Q : Subgroup C) : Set C) := by
    intro w hw
    rw [mem_centralizer_iff]
    intro q hq
    have hqS : (q : G) ∈ S₀ := by
      rw [← hQ]
      exact ⟨q, hq, rfl⟩
    exact Subtype.ext (mem_centralizer_iff.mp (hWS₀ (mem_subgroupOf.mp hw)) q hqS)
  have hf'2 : orderOf f' = 2 := by rwa [← Subgroup.orderOf_coe]
  have hg'o : Odd (orderOf g') := by rwa [← Subgroup.orderOf_coe]
  rcases normal_or_eq_bot_of_stronglyClosed hO' Q hXS' hXab' hX'32 hcl'
      (mem_subgroupOf.mpr hfX) hf'2 hfZ' hgX' hg'o hirr' hD2' hW'odd hWS' with hN | hWbot
  · intro c hc
    apply hNX
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    exact mem_subgroupOf.mp (hN.conj_mem ⟨x, hXC hx⟩ (mem_subgroupOf.mpr hx) ⟨c, hc⟩)
  · have hWb : W = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have h1 : (⟨w, hWC hw⟩ : C) ∈ W' := mem_subgroupOf.mpr hw
      rw [hWbot, mem_bot] at h1
      exact mem_bot.mpr (congrArg Subtype.val h1)
    rw [hWb, normalizer_eq_top_iff.mpr normal_bot]
    exact le_top

end Frame

end CFSG.ComponentClassification.GMS78
