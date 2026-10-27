module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA10Std
public import CFSG.LocalAnalysis.ComponentClassification.GSLitIsoTarget
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallS10V

public section

namespace CFSG.ComponentClassification.CatFactsSmall

namespace A10

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open Equiv

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)
  (eK : OddBar h.K ≃* alternatingGroup (Fin 10))

include hKa in
theorem mem_B_of_two_elt {w : h.W} (hwK : (w : H) ∈ coreActionKernel h.K) {a : ℕ}
    (hw : w ^ 2 ^ a = 1) : (w : H) ∈ h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : layerIn h.W = h.K := h.V_eq_K hKa
  set X := normalizer (h.B : Set H) ⊓ coreActionKernel (layerIn h.W) with hX
  obtain ⟨R, hR⟩ : ∃ R : Sylow 2 X, (R : Subgroup X) = h.B.subgroupOf X := h.B_sylow_kernel
  have hwX : (w : H) ∈ X := ⟨w.2, by rw [hV]; exact hwK⟩
  set x : X := ⟨w, hwX⟩ with hx
  have hw2H : (w : H) ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val hw
    simpa using this
  have hx2 : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := a) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [hx] using hw2H)))
  have hRn : x ∈ normalizer ((R : Subgroup X) : Set X) := by
    rw [hR, mem_normalizer_iff]
    intro b
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.1 w.2 b
  have hxR : x ∈ (R : Subgroup X) := by
    have hsup : IsPGroup 2 ↥((R : Subgroup X) ⊔ zpowers x) :=
      IsPGroup.to_sup_of_normal_left' R.isPGroup' hx2 (zpowers_le.2 hRn)
    rw [← R.is_maximal' hsup le_sup_left]
    exact mem_sup_right (mem_zpowers x)
  rw [hR, mem_subgroupOf] at hxR
  exact hxR

theorem mem_pPrimeCore_W_of_mem_pPrimeCore (hKN : h.W ≤ normalizer (h.K : Set H)) {k : h.K}
    (hk : k ∈ pPrimeCore 2 h.K) : (⟨k, K_le_W h k.2⟩ : h.W) ∈ pPrimeCore 2 h.W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup h.W := (pPrimeCore 2 h.K).map (inclusion (K_le_W h)) with hM
  have hMn : M.Normal := ⟨fun m hm w => by
    obtain ⟨o, ho, rfl⟩ := hm
    have hw := UnbalancedGS.normalizer_le_normalizer_map_of_characteristic h.K
      (pPrimeCore 2 h.K) (hKN w.2)
    obtain ⟨o', ho', hoe⟩ := mem_map.1 ((mem_normalizer_iff.1 hw (o : H)).1 ⟨o, ho, rfl⟩)
    refine ⟨o', ho', Subtype.ext ?_⟩
    rw [subtype_apply] at hoe
    simp only [coe_inclusion, coe_mul, coe_inv, hoe]⟩
  have hMc : Nat.Coprime 2 (Nat.card M) := by
    rw [hM, card_map_of_injective (inclusion_injective _)]
    exact pPrimeCore_coprime_card
  exact le_pPrimeCore_of_coprime hMn hMc ⟨k, hk, rfl⟩

theorem mem_oddCoreIn_K_of_rhoW_eq_one {k : h.K} (hk : rhoW h hKa eK ⟨k, K_le_W h k.2⟩ = 1) :
    (k : H) ∈ oddCoreIn h.K := by
  rw [rhoW_of_mem_K] at hk
  have h1 : (k : OddBar h.K) = 1 := eK.map_eq_one_iff.1 (Subtype.ext hk)
  exact ⟨k, (QuotientGroup.eq_one_iff k).1 h1, rfl⟩

omit [Finite H] in
theorem commute_of_fix_compl {τ σ l : Perm (Fin 10)} (hσ : ∀ x ∉ τ.support, σ x = x)
    (hl : ∀ x ∈ τ.support, l x = x) : σ * l = l * σ := by
  have hd : Perm.Disjoint σ l := fun x => by
    by_cases hx : x ∈ τ.support
    · exact Or.inr (hl x hx)
    · exact Or.inl (hσ x hx)
  exact hd.commute.eq

variable (eJ : OddBar h.J ≃* alternatingGroup (Fin 6))

include eJ in
theorem rhoW_commute_of_mem_P (hLcard : Nat.card (Lsub hKa eK) = 360) {t : h.W}
    (htJ : (t : H) ∈ normalizer (h.J : Set H)) (htB : (t : H) ∈ normalizer (h.B : Set H))
    (htP : (t : H) ∈ coreActionKernel h.J) :
    ∀ l ∈ Lsub hKa eK, l * rhoW h hKa eK t = rhoW h hKa eK t * l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK : JB ≤ h.K := JB_le_K hKa
  have hJBW : JB ≤ h.W := hJBK.trans (K_le_W h)
  have hOL : pPrimeCore 2 (Lsub hKa eK) = ⊥ := by
    have hO := card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 (Lsub hKa eK))
    rw [hLcard, card_L_core hKa eK eJ] at hO
    exact Subgroup.eq_bot_of_card_eq _ (by omega)
  have hθ : ∀ j : JB, rhoW h hKa eK (inclusion hJBW j) ∈ Lsub hKa eK := fun j =>
    ⟨wbarMk h.B (inclusion hJBW j), ⟨inclusion hJBW j, j.2, rfl⟩, rhoBar_mk _ _ _⟩
  set θ : JB →* Lsub hKa eK :=
    ((rhoW h hKa eK).comp (inclusion hJBW)).codRestrict (Lsub hKa eK) hθ with hθdef
  have hθs : Function.Surjective θ := by
    rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hx
    exact ⟨⟨x, hx⟩, Subtype.ext (rhoBar_mk hKa eK x).symm⟩
  have hθO : (pPrimeCore 2 JB).map θ = ⊥ := by
    have hn : ((pPrimeCore 2 JB).map θ).Normal := (pPrimeCore_normal (p := 2)).map _ hθs
    have hc : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 JB).map θ)) :=
      (pPrimeCore_coprime_card (p := 2) (G := JB)).coprime_dvd_right
        ((pPrimeCore 2 JB).card_map_dvd θ)
    rw [eq_bot_iff, ← hOL]
    exact le_pPrimeCore_of_coprime hn hc
  rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hj
  rw [rhoBar_mk]
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  have htJB : (t : H) ∈ normalizer (JB : Set H) := GSLit.mem_normalizer_fixedLayer htJ htB
  have hu1 : (t : H) * j * (t : H)⁻¹ * (j : H)⁻¹ ∈ JB :=
    mul_mem ((mem_normalizer_iff.1 htJB j).1 hj) (inv_mem hj)
  have hu2 : (t : H) * j * (t : H)⁻¹ * (j : H)⁻¹ ∈ (pPrimeCore 2 h.J).map h.J.subtype := by
    have h1 := (mem_coreActionKernel.1 (inv_mem htP)).2 _ (inv_mem (hJBJ hj))
    rw [inv_inv, inv_inv] at h1
    have h3 : (t : H) * j * (t : H)⁻¹ * (j : H)⁻¹ = ((j : H) * t * (j : H)⁻¹ * (t : H)⁻¹)⁻¹ := by
      group
    rw [h3]
    exact inv_mem h1
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := (isPGroup_S h).to_le (h.B_le.trans inf_le_left)
  have hOJB := (GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J h) hBJ hB2).2
  have hu : (t : H) * j * (t : H)⁻¹ * (j : H)⁻¹ ∈ (pPrimeCore 2 JB).map JB.subtype := by
    rw [hOJB]
    exact ⟨hu1, hu2⟩
  obtain ⟨o, ho, hoe⟩ := hu
  have hθo : θ o = 1 := by
    have : θ o ∈ (pPrimeCore 2 JB).map θ := ⟨o, ho, rfl⟩
    rw [hθO, mem_bot] at this
    exact this
  have h4 : rhoW h hKa eK (t * j * t⁻¹ * j⁻¹) = 1 := by
    have h5 : ((rhoW h hKa eK).comp (inclusion hJBW)) o = 1 := congrArg Subtype.val hθo
    have h7 : inclusion hJBW o = t * j * t⁻¹ * j⁻¹ := Subtype.ext (by
      rw [coe_inclusion]
      simpa using hoe)
    rw [← h7]
    exact h5
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h4
  have h6 := mul_inv_eq_one.1 h4
  rw [mul_inv_eq_iff_eq_mul] at h6
  exact h6.symm

include hKa in
theorem inf_oddCoreIn_K_le :
    GSLit.fixedLayer h.J h.B ⊓ oddCoreIn h.K ≤
      (pPrimeCore 2 (GSLit.fixedLayer h.J h.B)).map (GSLit.fixedLayer h.J h.B).subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK : JB ≤ h.K := JB_le_K hKa
  set N : Subgroup JB := (oddCoreIn h.K).subgroupOf JB with hN
  have hNn : N.Normal := ⟨fun n hn g => by
    rw [hN, mem_subgroupOf] at hn ⊢
    obtain ⟨o, ho, hoe⟩ := hn
    refine ⟨⟨g, hJBK g.2⟩ * o * ⟨g, hJBK g.2⟩⁻¹, (pPrimeCore_normal (p := 2)).conj_mem _ ho _, ?_⟩
    rw [subtype_apply] at hoe ⊢
    simp [hoe]⟩
  have hNc : Nat.Coprime 2 (Nat.card N) := by
    have h1 : Nat.card N ∣ Nat.card (oddCoreIn h.K) := by
      rw [← card_map_of_injective JB.subtype_injective]
      exact card_dvd_of_le (by
        rintro _ ⟨x, hx, rfl⟩
        exact hx)
    have h2 : Nat.card (oddCoreIn h.K) = Nat.card (pPrimeCore 2 h.K) :=
      card_map_of_injective h.K.subtype_injective
    rw [h2] at h1
    exact (pPrimeCore_coprime_card (p := 2) (G := h.K)).coprime_dvd_right h1
  rintro x ⟨hx1, hx2⟩
  exact ⟨⟨x, hx1⟩, le_pPrimeCore_of_coprime hNn hNc (show (⟨x, hx1⟩ : JB) ∈ N from hx2), rfl⟩

theorem mem_coreActionKernel_J_of_commute {r : h.W} (hrJ : (r : H) ∈ normalizer (h.J : Set H))
    (hrB : (r : H) ∈ normalizer (h.B : Set H))
    (hc : ∀ l ∈ Lsub hKa eK, l * rhoW h hKa eK r = rhoW h hKa eK r * l) :
    (r : H) ∈ coreActionKernel h.J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK : JB ≤ h.K := JB_le_K hKa
  have hJBW : JB ≤ h.W := hJBK.trans (K_le_W h)
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  have hrJB : (r : H) ∈ normalizer (JB : Set H) := GSLit.mem_normalizer_fixedLayer hrJ hrB
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := (isPGroup_S h).to_le (h.B_le.trans inf_le_left)
  obtain ⟨hsup, hOJB⟩ := GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J h) hBJ hB2
  have hw : ∀ j ∈ JB, (r : H) * j * (r : H)⁻¹ * j⁻¹ ∈ (pPrimeCore 2 h.J).map h.J.subtype := by
    intro j hj
    have hw1 : (r : H) * j * (r : H)⁻¹ * j⁻¹ ∈ JB :=
      mul_mem ((mem_normalizer_iff.1 hrJB j).1 hj) (inv_mem hj)
    have hwK : (r : H) * j * (r : H)⁻¹ * j⁻¹ ∈ h.K := hJBK hw1
    have hl : rhoW h hKa eK ⟨j, hJBW hj⟩ ∈ Lsub hKa eK :=
      ⟨wbarMk h.B ⟨j, hJBW hj⟩, ⟨⟨j, hJBW hj⟩, hj, rfl⟩, rhoBar_mk _ _ _⟩
    have hρ : rhoW h hKa eK ⟨(⟨_, hwK⟩ : h.K), K_le_W h hwK⟩ = 1 := by
      have he : (⟨(⟨_, hwK⟩ : h.K), K_le_W h hwK⟩ : h.W) =
          r * ⟨j, hJBW hj⟩ * r⁻¹ * (⟨j, hJBW hj⟩ : h.W)⁻¹ := Subtype.ext (by simp)
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc _ hl]
      group
    have hwO := mem_oddCoreIn_K_of_rhoW_eq_one hKa eK hρ
    have := inf_oddCoreIn_K_le hKa ⟨hw1, hwO⟩
    rw [hOJB] at this
    exact this.2
  refine mem_coreActionKernel_of_oddBarConj_eq_one (g := ⟨(r : H), hrJ⟩) ?_
  obtain ⟨-, e1, he1⟩ := restriction_quotient_mulEquiv hJBJ hsup
  ext x
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (e1.symm x)
  have hx : x = ((⟨t, hJBJ t.2⟩ : h.J) : OddBar h.J) := by
    rw [← he1 t (hJBJ t.2), ht, MulEquiv.apply_symm_apply]
  rw [hx, oddBarConj_apply_mk, MulAut.one_apply, QuotientGroup.eq]
  obtain ⟨o, ho, hoe⟩ := hw t t.2
  rw [subtype_apply] at hoe
  have heq : (⟨(r : H) * t * (r : H)⁻¹, (mem_normalizer_iff.mp hrJ t).mp (hJBJ t.2)⟩ : h.J)⁻¹ *
      ⟨t, hJBJ t.2⟩ = (⟨t, hJBJ t.2⟩ : h.J)⁻¹ * o⁻¹ * ⟨t, hJBJ t.2⟩ := by
    apply Subtype.ext
    simp only [coe_mul, coe_inv, hoe]
    group
  rw [heq]
  have := (pPrimeCore_normal (p := 2) (G := h.J)).conj_mem _ (inv_mem ho) (⟨t, hJBJ t.2⟩ : h.J)⁻¹
  rwa [inv_inv] at this

abbrev Esub (h : Hyp52 H) : Subgroup H := GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W

include hKa in
theorem mem_normalizer_E_of_commute {k : h.K}
    (hc : ∀ l ∈ Lsub hKa eK,
      l * rhoW h hKa eK ⟨k, K_le_W h k.2⟩ = rhoW h hKa eK ⟨k, K_le_W h k.2⟩ * l) :
    (k : H) ∈ normalizer (Esub h : Set H) := by
  have hKN := W_le_normalizer_K h hKa
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK : JB ≤ h.K := JB_le_K hKa
  have hJBW : JB ≤ h.W := hJBK.trans (K_le_W h)
  have hle : Esub h ≤ (Esub h).comap (MulAut.conj (k : H)).toMonoidHom := by
    refine sup_le (fun j hj => ?_) (fun o ho => ?_)
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hwK : (k : H) * j * (k : H)⁻¹ * j⁻¹ ∈ h.K :=
        mul_mem (mul_mem (mul_mem k.2 (hJBK hj)) (inv_mem k.2)) (inv_mem (hJBK hj))
      have hl : rhoW h hKa eK ⟨j, hJBW hj⟩ ∈ Lsub hKa eK :=
        ⟨wbarMk h.B ⟨j, hJBW hj⟩, ⟨⟨j, hJBW hj⟩, hj, rfl⟩, rhoBar_mk _ _ _⟩
      have hρ : rhoW h hKa eK ⟨(⟨_, hwK⟩ : h.K), K_le_W h hwK⟩ = 1 := by
        have he : (⟨(⟨_, hwK⟩ : h.K), K_le_W h hwK⟩ : h.W) =
            ⟨k, K_le_W h k.2⟩ * ⟨j, hJBW hj⟩ * (⟨k, K_le_W h k.2⟩ : h.W)⁻¹ *
              (⟨j, hJBW hj⟩ : h.W)⁻¹ := Subtype.ext (by simp)
        rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc _ hl]
        group
      obtain ⟨o, ho, hoe⟩ := mem_oddCoreIn_K_of_rhoW_eq_one hKa eK hρ
      rw [subtype_apply] at hoe
      have hoW := mem_pPrimeCore_W_of_mem_pPrimeCore hKN ho
      have h1 : (k : H) * j * (k : H)⁻¹ = ((k : H) * j * (k : H)⁻¹ * j⁻¹) * j := by group
      rw [h1]
      refine mul_mem (mem_sup_right ⟨_, hoW, ?_⟩) (mem_sup_left hj)
      rw [subtype_apply]
      exact hoe
    · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      obtain ⟨o', ho', rfl⟩ := ho
      refine mem_sup_right ⟨⟨k, K_le_W h k.2⟩ * o' * (⟨k, K_le_W h k.2⟩ : h.W)⁻¹,
        (pPrimeCore_normal (p := 2)).conj_mem _ ho' _, ?_⟩
      simp
  exact mem_normalizer_of_conj_le fun g hg => hle hg

include hKa in
theorem rhoW_mem_normalizer_L {y : h.W} (hy : (y : H) ∈ normalizer (Esub h : Set H)) :
    rhoW h hKa eK y ∈
      normalizer ((Lsub hKa eK : Subgroup (Perm (Fin 10))) : Set (Perm (Fin 10))) := by
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBW : JB ≤ h.W := (JB_le_K hKa).trans (K_le_W h)
  set Z : Subgroup H := ((Lsub hKa eK).comap (rhoW h hKa eK)).map h.W.subtype with hZ
  have hEZ : Esub h ≤ Z := by
    refine sup_le (fun j hj => ⟨⟨j, hJBW hj⟩, ?_, rfl⟩) (fun o ho => ?_)
    · exact ⟨wbarMk h.B ⟨j, hJBW hj⟩, ⟨⟨j, hJBW hj⟩, hj, rfl⟩, rhoBar_mk _ _ _⟩
    · obtain ⟨o', ho', rfl⟩ := ho
      refine ⟨o', ?_, rfl⟩
      have h1 : rhoW h hKa eK o' = 1 := oddTwoCore_le_ker hKa eK (pPrimeCore_le_oddTwoCore' ho')
      show rhoW h hKa eK o' ∈ Lsub hKa eK
      rw [h1]
      exact one_mem _
  have hEL : ∀ e : h.W, (e : H) ∈ Esub h → rhoW h hKa eK e ∈ Lsub hKa eK := by
    intro e he
    obtain ⟨e', he', hee⟩ := hEZ he
    have : e' = e := Subtype.ext hee
    rw [← this]
    exact he'
  apply mem_normalizer_of_conj_le
  rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hj
  rw [rhoBar_mk, ← map_inv, ← map_mul, ← map_mul]
  apply hEL
  exact (mem_normalizer_iff.1 hy j).1 (mem_sup_left hj)

theorem T_le_W : h.T ≤ h.W := fun _ ht => ht.1.2

theorem isPGroup_T : IsPGroup 2 h.T := (isPGroup_S h).to_le (fun _ ht => ht.1.1)

include hKa in
theorem rhoW_T_eq_one_iff (t : h.T) :
    rhoW h hKa eK (inclusion T_le_W t) = 1 ↔ (t : H) ∈ h.B := by
  rw [rhoW_eq_one_iff]
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := isPGroup_T t
    exact mem_B_of_two_elt hKa (w := inclusion T_le_W t) ht (by rw [← map_pow, ha, map_one])
  · intro hb
    have := (h.B_le_kernel hb).2
    rwa [show layerIn h.W = h.K from h.V_eq_K hKa] at this

include eJ in
theorem rhoW_T_mem_fourGroup {τ : Perm (Fin 10)} (h4 : τ.support.card = 4)
    (hL : ∀ l, l ∈ Lsub hKa eK ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    (hLcard : Nat.card (Lsub hKa eK) = 360) (t : h.T) :
    rhoW h hKa eK (inclusion T_le_W t) ∈ fourGroup h4 := by
  have hF4 : 4 ≤ τ.supportᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin, h4]
    norm_num
  have htS : (t : H) ∈ h.S := t.2.1.1
  have hcomm := rhoW_commute_of_mem_P hKa eK eJ hLcard (t := inclusion T_le_W t)
    (h.S_le htS).2 t.2.1.2 t.2.2.2
  obtain ⟨a, ha⟩ := isPGroup_T t
  refine mem_fourGroup_of_two_elt h4
    (Equiv.Perm.mem_alternatingGroup.2 (sign_rhoW hKa eK eJ _))
    (fix_of_commute_alt hF4 hL hcomm) (e := a) ?_
  rw [← map_pow, ← map_pow, ha, map_one, map_one]

theorem exists_T_K_of_mem_fourGroup {τ : Perm (Fin 10)} (h4 : τ.support.card = 4)
    (hL : ∀ l, l ∈ Lsub hKa eK ↔ l ∈ alternatingGroup (Fin 10) ∧ ∀ x ∈ τ.support, l x = x)
    {v : Perm (Fin 10)} (hv : v ∈ fourGroup h4) :
    ∃ t : h.W, (t : H) ∈ h.T ⊓ h.K ∧ rhoW h hKa eK t = v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV : layerIn h.W = h.K := h.V_eq_K hKa
  set Y := layerIn h.W ⊓
    normalizer ((GSLit.fixedLayer h.J h.B ⊔ oddCoreIn h.W : Subgroup H) : Set H) with hY
  obtain ⟨R, hRQ, -, R', hR'⟩ := h.sylow_layer
  have hYW : Y ≤ h.W := fun y hy => K_le_W h (by rw [← hV]; exact hy.1)
  set ψ : Y →* Perm (Fin 10) := (rhoW h hKa eK).comp (inclusion hYW) with hψ
  have hVY : ∀ v ∈ fourGroup h4, v ∈ ψ.range := by
    intro v hv
    obtain ⟨hvA, hvfix, -⟩ := (mem_fourGroup h4 v).1 hv
    obtain ⟨k, hk⟩ := exists_lift_alt hKa eK hvA
    have hcomm : ∀ l ∈ Lsub hKa eK, l * rhoW h hKa eK ⟨k, K_le_W h k.2⟩ =
        rhoW h hKa eK ⟨k, K_le_W h k.2⟩ * l := by
      intro l hl
      rw [hk]
      exact (commute_of_fix_compl hvfix ((hL l).1 hl).2).symm
    have hkY : (k : H) ∈ Y := ⟨by
      show (k : H) ∈ layerIn h.W
      rw [hV]
      exact k.2, mem_normalizer_E_of_commute hKa eK hcomm⟩
    exact ⟨⟨k, hkY⟩, hk⟩
  set V' := (fourGroup h4).subgroupOf ψ.range with hV'
  have hV'n : V'.Normal := ⟨fun n hn g => by
    obtain ⟨_, y, rfl⟩ := g
    rw [hV', mem_subgroupOf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact conj_mem_fourGroup h4 hL (rhoW_mem_normalizer_L hKa eK y.2.2) hn⟩
  have hV'2 : IsPGroup 2 V' := fun x => ⟨1, by
    apply Subtype.ext
    apply Subtype.ext
    have := ((mem_fourGroup h4 _).1 (mem_subgroupOf.1 x.2)).2.2
    simpa [pow_one, sq] using this⟩
  set P' := R'.mapSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective with hP'
  have hV'P : V' ≤ (P' : Subgroup ψ.range) := by
    have hsup : IsPGroup 2 ↥((P' : Subgroup ψ.range) ⊔ V') :=
      IsPGroup.to_sup_of_normal_right' P'.isPGroup' hV'2
        (by rw [@normalizer_eq_top _ _ V' hV'n]; exact le_top)
    rw [← P'.is_maximal' hsup le_sup_left]
    exact le_sup_right
  have hvP := hV'P (show (⟨v, hVY v hv⟩ : ψ.range) ∈ V' from mem_subgroupOf.2 hv)
  rw [hP', Sylow.coe_mapSurjective] at hvP
  obtain ⟨r, hr, hre⟩ := hvP
  have hrv : ψ r = v := congrArg Subtype.val hre
  have hr' : r ∈ (R' : Subgroup Y) := hr
  rw [hR', mem_subgroupOf] at hr'
  have hrQ := hRQ hr'
  have hrP : (r : H) ∈ coreActionKernel h.J := by
    refine mem_coreActionKernel_J_of_commute hKa eK (r := inclusion hYW r) (h.S_le hrQ.1).2
      hrQ.2 fun l hl => ?_
    have : rhoW h hKa eK (inclusion hYW r) = v := hrv
    rw [this]
    exact (commute_of_fix_compl ((mem_fourGroup h4 v).1 hv).2.1 ((hL l).1 hl).2).symm
  have hrK : (r : H) ∈ h.K := by
    rw [← hV]
    exact r.2.1
  exact ⟨inclusion hYW r, ⟨⟨hrQ, ⟨hrQ.1, hrP⟩⟩, hrK⟩, hrv⟩

include hKa eK eJ in
theorem prop21 : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 4 ∧ ∀ t ∈ h.T, t ^ 2 ∈ h.B := by
  obtain ⟨τ, -, -, -, h4, hL, hLcard⟩ := exists_std_tau hKa eK eJ
  set φ : h.T →* Perm (Fin 10) := (rhoW h hKa eK).comp (inclusion T_le_W) with hφ
  have hker : φ.ker = h.B.subgroupOf h.T := by
    ext t
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, rhoW_T_eq_one_iff hKa eK, mem_subgroupOf]
  have hφrange : φ.range = fourGroup h4 := by
    ext v
    constructor
    · rintro ⟨t, rfl⟩
      exact rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard t
    · intro hv
      obtain ⟨t, ht, htv⟩ := exists_T_K_of_mem_fourGroup hKa eK h4 hL hv
      exact ⟨⟨t, ht.1⟩, htv⟩
  refine ⟨?_, fun t ht => ?_⟩
  · rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hφrange,
      card_fourGroup]
  · have h1 : φ (⟨t, ht⟩ ^ 2) = 1 := by
      rw [map_pow, sq]
      exact ((mem_fourGroup h4 _).1 (rhoW_T_mem_fourGroup hKa eK eJ h4 hL hLcard ⟨t, ht⟩)).2.2
    have h2 : (⟨t, ht⟩ : h.T) ^ 2 ∈ h.B.subgroupOf h.T := by
      rw [← hker]
      exact h1
    rw [mem_subgroupOf] at h2
    simpa using h2

end A10

open CFSG.ComponentClassification.GSThmB A10 in
theorem cfProp21A10 : CFProp21A10 := by
  intro H _ _ h hrow
  obtain ⟨⟨eJ⟩, hKa, ⟨eK⟩⟩ := hrow
  exact prop21 hKa eK eJ

end CFSG.ComponentClassification.CatFactsSmall
