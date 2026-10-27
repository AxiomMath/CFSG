module

public import CFSG.Goldschmidt.Steps.G36Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
import CFSG.Goldschmidt.Steps.G76U34
import CFSG.Goldschmidt.Steps.G76Aut
import CFSG.Goldschmidt.Steps.G36TypeIMain
import CFSG.Goldschmidt.Steps.G3aGlue
import CFSG.Goldschmidt.Steps.G74Basic
import CFSG.Walter.Bender1970.S38.Basic
import CFSG.Walter.W67.Section5.Sylow52
import CFSG.Walter.W67.W1Basic
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.Helpers

public section

namespace CFSG.Goldschmidt

namespace G76

open CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Conj

omit [Finite G] in
theorem mem_normalizer_subgroupOf {K Y : Subgroup G} {y : K}
    (h : (y : G) ∈ Subgroup.normalizer (Y : Set G)) :
    y ∈ Subgroup.normalizer ((Y.subgroupOf K : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  change (k : G) ∈ Y ↔ ((y * k * y⁻¹ : K) : G) ∈ Y
  push_cast
  exact Subgroup.mem_normalizer_iff.mp h k

omit [Finite G] in
theorem conj_mem_normalizer_map {X : Subgroup G} {g : G} (c : G)
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    c * g * c⁻¹ ∈
      Subgroup.normalizer ((X.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g * y * g⁻¹, (hg y).mp hy, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy, hyx⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have := (hg (g⁻¹ * y * g)).mpr (by simpa [mul_assoc] using hy)
      exact this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hx : x = (c * g * c⁻¹)⁻¹ * (c * y * c⁻¹) * (c * g * c⁻¹) := by
        rw [hyx]; group
      rw [hx]
      group

end Conj

section Sylow

theorem sylow_facts
    {K V T : Subgroup G} (hKq : CFSG.Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* PSU3 2 2)
    (hZ2 : ∀ z ∈ Subgroup.center K, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hVK : V ≤ K) (hV4 : Nat.card V = 4) (hT2 : IsPGroup 2 T)
    (hTmax : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T)
    (hTN : T ≤ Subgroup.normalizer (K : Set G))
    (hTV : T ≤ Subgroup.centralizer (V : Set G)) (hVT : V ≤ T) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = T ⊓ K ∧
      (V.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center K)) =
        sylowCenter ((P.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center K)) :
          Sylow 2 (K ⧸ Subgroup.center K)) : Subgroup (K ⧸ Subgroup.center K)) ∧
      Nat.card (T ⊓ K : Subgroup G) = 64 ∧
      V ≤ ⁅T ⊓ K, T ⊓ K⁆ ∧
      ∃ r ∈ K, r ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ∧
        r ∈ Subgroup.centralizer (V : Set G) ∧
        ∀ X : Subgroup G, X ≤ T ⊓ K → T ⊓ K ≤ Subgroup.normalizer (X : Set G) →
          r ∈ Subgroup.normalizer (X : Set G) → X ≤ V ∨ X = T ⊓ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS : fusionIsSylowIn 2 T (Subgroup.normalizer (K : Set G)) :=
    ⟨hTN, hT2, fun P _ hP2 hTP => hTmax P hP2 hTP⟩
  have hKN : (K.subgroupOf (Subgroup.normalizer (K : Set G))).IsSubnormal :=
    (Subgroup.normal_in_normalizer).isSubnormal
  have hTK := G3a.fusionIsSylowIn_inf hTS Subgroup.le_normalizer hKN
  obtain ⟨P, hP⟩ := G3a.exists_sylow_of_fusionIsSylowIn hTK
  have hPmap : (P : Subgroup K).map K.subtype = T ⊓ K := by
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_of_le_left inf_le_right]
  have hmemP : ∀ x : K, x ∈ (P : Subgroup K) ↔ (x : G) ∈ T ⊓ K := by
    intro x
    rw [hP, Subgroup.mem_subgroupOf]
  obtain ⟨hc64, hcZ4, hcomm, hmapZ, r', hr'N, hr'Z, hX⟩ :=
    psu34_sylow_facts G32 hKq e hZ2 P
  set ZP := (P : Subgroup K) ⊓ Subgroup.centralizer ((P : Subgroup K) : Set K) with hZPdef
  have hA₀ : V.subgroupOf K = ZP := by
    have hle : V.subgroupOf K ≤ ZP := by
      intro v hv
      rw [Subgroup.mem_subgroupOf] at hv
      refine ⟨(hmemP v).mpr ⟨hVT hv, v.2⟩, Subgroup.mem_centralizer_iff.mpr fun p hp => ?_⟩
      have h1 := (hmemP p).mp hp
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hTV h1.1) v hv).symm
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hcZ4, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV4]
  have hmapV : (V.subgroupOf K).map K.subtype = V := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hVK]
  refine ⟨P, hPmap, by rw [hA₀]; exact hmapZ, ?_, ?_, r', r'.2, ?_, ?_, ?_⟩
  · rw [← hPmap, Subgroup.card_map_of_injective K.subtype_injective, hc64]
  · rw [← hPmap, ← Subgroup.map_commutator, hcomm, ← hA₀, hmapV]
  · apply CFSG.Walter.mem_normalizer_of_conj_mem'
    intro x hx
    have h1 := (Subgroup.mem_normalizer_iff.mp hr'N ⟨x, hx.2⟩).mp ((hmemP _).mpr hx)
    exact (hmemP _).mp h1
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : (⟨v, hVK hv⟩ : K) ∈ ZP := by
      rw [← hA₀]
      exact hv
    exact (congrArg Subtype.val (hr'Z _ hv')).symm
  · intro X hXT hTX hrX
    set X' := X.subgroupOf K with hX'
    have hX'P : X' ≤ P := fun x hx => (hmemP x).mpr (hXT (Subgroup.mem_subgroupOf.mp hx))
    have hPX' : (P : Subgroup K) ≤ Subgroup.normalizer (X' : Set K) := fun p hp =>
      mem_normalizer_subgroupOf (hTX ((hmemP p).mp hp))
    have hr'X' : r' ∈ Subgroup.normalizer (X' : Set K) := mem_normalizer_subgroupOf hrX
    have hXK : X ≤ K := hXT.trans inf_le_right
    have hmapX : X'.map K.subtype = X := by
      rw [hX', Subgroup.subgroupOf_map_subtype, inf_of_le_left hXK]
    rcases hX X' hX'P hPX' hr'X' with h | h
    · left
      intro x hx
      have hx' : (⟨x, hXK hx⟩ : K) ∈ ZP := h (Subgroup.mem_subgroupOf.mpr hx)
      rw [← hA₀] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
    · right
      rw [← hmapX, h, hPmap]

end Sylow

section Main

variable {S : Sylow 2 G} {A : Subgroup G}

omit [Finite G] in
theorem conj_mem_centralizer {n c : G} (hn : n ∈ Subgroup.normalizer (A : Set G))
    (hc : c ∈ Subgroup.centralizer (A : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : n⁻¹ * x * n ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x).mp hx
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hc _ hx'
  calc x * (n * c * n⁻¹) = n * ((n⁻¹ * x * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * x * n)) * n⁻¹ := by rw [h1]
    _ = n * c * n⁻¹ * x := by group

omit [Finite G] in
theorem mem_centralizer_of_decomp {K : Subgroup G}
    (hdec : A = A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G)) {r : G} (hrK : r ∈ K)
    (hrV : r ∈ Subgroup.centralizer ((A ⊓ K : Subgroup G) : Set G)) :
    r ∈ Subgroup.centralizer (A : Set G) := by
  have hle : A ≤ Subgroup.centralizer ({r} : Set G) := by
    rw [hdec]
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hrV x hx)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx.2 r hrK).symm
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem false_of_typeI
    (hG : GoldSetting G S A) (hA8 : Nat.card A = 8)
    {a : G} (haA : a ∈ A) {K : Subgroup G}
    (hKq : CFSG.Open.IsQuasisimple K) (hI : IsGoldTypeI K)
    (hT₀ : ∃ T₀ : Sylow 2 K, G36Hyp K (A.subgroupOf K) T₀)
    (hC2 : Nat.card (A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) = 2)
    (hdec : A = A ⊓ K ⊔ A ⊓ Subgroup.centralizer (K : Set G))
    (hCK : Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hSA : (S : Subgroup G) ≤ Subgroup.centralizer (A : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀, h⟩ := hT₀
  set π := QuotientGroup.mk' (Subgroup.center K) with hπ
  set V := A ⊓ K with hVdef
  set CA := A ⊓ Subgroup.centralizer (K : Set G) with hCAdef
  have hVK : V ≤ K := inf_le_right
  have hVA : V ≤ A := inf_le_left
  obtain ⟨hcard, -⟩ := CFSG.Walter.W67.card_sup_mul_card_inf_of_commute V CA
    (G74.comm_of_le hG.elem.1 inf_le_left inf_le_left)
  rw [← hdec, hA8, hC2] at hcard
  set A₀ := A.subgroupOf K with hA₀
  have hker : Nat.card (A₀.map π) * Nat.card (Subgroup.center K ⊓ A₀ : Subgroup K) =
      Nat.card A₀ := by
    rw [← Subgroup.relIndex_ker A₀ π, hπ, QuotientGroup.ker_mk']
    exact Subgroup.relIndex_mul_card _ _
  have hcenter : Nat.card (Subgroup.center K ⊓ A₀ : Subgroup K) =
      Nat.card (V ⊓ CA : Subgroup G) := by
    have heq : (Subgroup.center K ⊓ A₀).map K.subtype = V ⊓ CA := by
      ext x
      constructor
      · rintro ⟨y, ⟨hyZ, hyA⟩, rfl⟩
        refine ⟨⟨hyA, y.2⟩, hyA, Subgroup.mem_centralizer_iff.mpr fun k hk => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hyZ ⟨k, hk⟩)
      · rintro ⟨⟨hxA, hxK⟩, -, hxC⟩
        refine ⟨⟨x, hxK⟩, ⟨Subgroup.mem_center_iff.mpr fun k => Subtype.ext ?_, hxA⟩, rfl⟩
        exact Subgroup.mem_centralizer_iff.mp hxC k k.2
    rw [← Subgroup.card_map_of_injective K.subtype_injective, heq]
  have hA₀card : Nat.card A₀ = Nat.card V := by
    rw [hA₀, hVdef, ← Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.subgroupOf_map_subtype]
  have hmap4 : Nat.card (A₀.map π) = 4 := by
    have hpos : 0 < Nat.card (V ⊓ CA : Subgroup G) := Nat.card_pos
    rw [hcenter, hA₀card] at hker
    nlinarith
  have : IsSimpleGroup (K ⧸ Subgroup.center K) := hKq.2
  have hnab : ∃ x y : K ⧸ Subgroup.center K, x * y ≠ y * x :=
    Helpers.quasisimple_central_quotient_nonabelian K hKq
  have hZb : Subgroup.center (K ⧸ Subgroup.center K) = ⊥ :=
    Helpers.center_eq_bot (K ⧸ Subgroup.center K) hnab
  have hI' : IsGoldTypeI (K ⧸ Subgroup.center K) := isGoldTypeI_quotient_center hZb hI
  obtain ⟨D, y, hB⟩ := exists_g36Borel G32 h hI
  have hZTb : Nat.card ((T₀ : Subgroup K).map π ⊓
      Subgroup.centralizer (((T₀ : Subgroup K).map π : Subgroup _) : Set _) :
        Subgroup (K ⧸ Subgroup.center K)) = 4 := by
    rw [← hB.map_eq]
    exact hmap4
  set Tb' : Sylow 2 (K ⧸ Subgroup.center K) := T₀.mapSurjective (QuotientGroup.mk'_surjective _)
    with hTb'
  have hTb'coe : (Tb' : Subgroup (K ⧸ Subgroup.center K)) = (T₀ : Subgroup K).map π :=
    Sylow.coe_mapSurjective _ _
  obtain ⟨D', -, -, -, -, -, -, -, -, -, -, hPSL, -, hU, -, -, -, -, -⟩ :=
    G32 (K ⧸ Subgroup.center K) hI' Tb'
  rw [hTb'coe] at hPSL hU
  have e₂ : Nonempty (K ⧸ Subgroup.center K ≃* PSU3 2 2) := by
    rcases hI with ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exfalso
      have hab := isMulCommutative_map_of_psl2 (T₀ := T₀) (by omega) e
      have hle : (T₀ : Subgroup K).map π ≤ (T₀ : Subgroup K).map π ⊓
          Subgroup.centralizer (((T₀ : Subgroup K).map π : Subgroup _) : Set _) :=
        fun x hx => ⟨hx, Subgroup.mem_centralizer_iff.mpr fun z hz =>
          congrArg Subtype.val (hab.is_comm.comm ⟨z, hz⟩ ⟨x, hx⟩)⟩
      have h1 := Subgroup.card_le_of_le hle
      rw [hZTb, (hPSL n hn ⟨e⟩).1] at h1
      have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    · exfalso
      have h1 := (hB.sz n hn ⟨e⟩).1
      rw [hB.tb_eq, hZTb] at h1
      have : 2 ^ 3 ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have h1 := (hU n hn ⟨e⟩).1
      rw [hZTb] at h1
      have hn2 : n = 2 := by
        have : (2 : ℕ) ^ n = 2 ^ 2 := by rw [← h1]; norm_num
        exact Nat.pow_right_injective le_rfl this
      subst hn2
      exact ⟨e⟩
  obtain ⟨e⟩ := e₂
  have hZ2 := center_two_eq_one_of_psu3 hKq e
  have hQ : fusionIsBenderGroup (K ⧸ Subgroup.center K) := Or.inr (Or.inl ⟨2, le_rfl, ⟨e⟩⟩)
  have hX2 : ∀ x ∈ K, x ∈ Subgroup.centralizer (K : Set G) → ∀ k : ℕ, x ^ 2 ^ k = 1 →
      x = 1 := by
    intro x hxK hxC k hk
    have h1 := hZ2 ⟨x, hxK⟩ (Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp hxC g g.2)) k (Subtype.ext (by simpa using hk))
    exact congrArg Subtype.val h1
  have hVCA : V ⊓ CA = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact hX2 x hx.1.2 hx.2.2 1 (by rw [pow_one]; exact hG.elem.2 x hx.1.1)
  have hV4 : Nat.card V = 4 := by
    rw [hVCA, Subgroup.card_bot] at hcard
    omega
  set T := (S : Subgroup G) with hTdef
  have hCAN : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA)).trans hCK
  have hCAV : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.centralizer_le hVA
  have hAT : A ≤ T := hG.le
  have hVT : V ≤ T := hVA.trans hAT
  have hTmax : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T := fun P hP hTP =>
    S.is_maximal' hP hTP
  obtain ⟨P, hPmap, hmapV, hTK64, hVcomm, r, hrK, hrN, hrV, hrX⟩ :=
    sylow_facts hKq e hZ2 hVK hV4 S.isPGroup' hTmax (hSA.trans hCAN) (hSA.trans hCAV) hVT
  set TK := T ⊓ K with hTKdef
  have hrA : r ∈ Subgroup.centralizer (A : Set G) := mem_centralizer_of_decomp hdec hrK hrV
  obtain ⟨n, hnN, hnV⟩ : ∃ n ∈ Subgroup.normalizer (A : Set G),
      V.map (MulAut.conj n).toMonoidHom ≠ V := by
    by_contra hcon
    push Not at hcon
    have hle : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (V : Set G) := fun n hn =>
      CFSG.Walter.map_conj_eq_iff_mem_normalizer.mp (hcon n hn)
    rcases hG.irreducible V hVA hle with h0 | h0
    · rw [h0, Subgroup.card_bot] at hV4
      omega
    · rw [h0, hA8] at hV4
      omega
  set Kb := K.map (MulAut.conj n).toMonoidHom with hKbdef
  set Vb := V.map (MulAut.conj n).toMonoidHom with hVbdef
  have hAn : A.map (MulAut.conj n).toMonoidHom = A :=
    CFSG.Walter.map_conj_eq_iff_mem_normalizer.mpr hnN
  have hVb : A ⊓ Kb = Vb := by
    rw [hVbdef, hVdef, Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective, hAn]
  have hV4b : Nat.card Vb = 4 := by
    rw [hVbdef, Subgroup.card_map_of_injective (MulAut.conj n).injective, hV4]
  have hCANb : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (Kb : Set G) := by
    intro g hg
    have h1 : n⁻¹ * g * n⁻¹⁻¹ ∈ Subgroup.centralizer (A : Set G) :=
      conj_mem_centralizer (Subgroup.inv_mem _ hnN) hg
    have h2 := conj_mem_normalizer_map n (hCAN h1)
    have e1 : n * (n⁻¹ * g * n⁻¹⁻¹) * n⁻¹ = g := by group
    rwa [e1] at h2
  set T' := T.map (MulAut.conj n⁻¹).toMonoidHom with hT'def
  have hT'2 : IsPGroup 2 T' := S.isPGroup'.map _
  have hT'max : ∀ Q : Subgroup G, IsPGroup 2 Q → T' ≤ Q → Q = T' := by
    intro Q hQ hTQ
    have h1 : T ≤ Q.map (MulAut.conj n).toMonoidHom := by
      calc T = T'.map (MulAut.conj n).toMonoidHom :=
            (CFSG.Walter.map_conj_inv_map_conj n T).symm
        _ ≤ Q.map (MulAut.conj n).toMonoidHom := Subgroup.map_mono hTQ
    have h2 := hTmax _ (hQ.map _) h1
    rw [← CFSG.Walter.map_conj_map_conj_inv n Q, h2]
  have hT'C : T' ≤ Subgroup.centralizer (A : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact conj_mem_centralizer (Subgroup.inv_mem _ hnN) (hSA ht)
  have hVT' : V ≤ T' := by
    intro v hv
    have hv' : n * v * n⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hnN v).mp (hVA hv)
    refine ⟨n * v * n⁻¹, hAT hv', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  obtain ⟨-, -, -, hT'K64, -, r'', hr''K, hr''N, hr''V, hr''X⟩ :=
    sylow_facts hKq e hZ2 hVK hV4 hT'2 hT'max (hT'C.trans hCAN) (hT'C.trans hCAV) hVT'
  have hr''A : r'' ∈ Subgroup.centralizer (A : Set G) :=
    mem_centralizer_of_decomp hdec hr''K hr''V
  set TKb := T ⊓ Kb with hTKbdef
  have hTKb : (T' ⊓ K).map (MulAut.conj n).toMonoidHom = TKb := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj n).injective, hT'def,
      CFSG.Walter.map_conj_inv_map_conj]
  have hTKb64 : Nat.card TKb = 64 := by
    rw [← hTKb, Subgroup.card_map_of_injective (MulAut.conj n).injective, hT'K64]
  set r' := n * r'' * n⁻¹ with hr'def
  have hr'N : r' ∈ Subgroup.normalizer (TKb : Set G) := by
    rw [← hTKb]
    exact conj_mem_normalizer_map n hr''N
  have hr'A : r' ∈ Subgroup.centralizer (A : Set G) := conj_mem_centralizer hnN hr''A
  have hr'X : ∀ X : Subgroup G, X ≤ TKb → TKb ≤ Subgroup.normalizer (X : Set G) →
      r' ∈ Subgroup.normalizer (X : Set G) → X ≤ Vb ∨ X = TKb := by
    intro X hX hTX hrX
    set X' := X.map (MulAut.conj n⁻¹).toMonoidHom with hX'
    have hXX' : X'.map (MulAut.conj n).toMonoidHom = X := CFSG.Walter.map_conj_inv_map_conj n X
    have hX'le : X' ≤ T' ⊓ K := by
      rw [← CFSG.Walter.map_conj_map_conj_inv n (T' ⊓ K), hTKb]
      exact Subgroup.map_mono hX
    have hTX' : T' ⊓ K ≤ Subgroup.normalizer (X' : Set G) := by
      intro t ht
      have h1 : n * t * n⁻¹ ∈ TKb := by
        rw [← hTKb]
        exact ⟨t, ht, rfl⟩
      have h2 := conj_mem_normalizer_map n⁻¹ (hTX h1)
      have e1 : n⁻¹ * (n * t * n⁻¹) * n⁻¹⁻¹ = t := by group
      rwa [e1] at h2
    have hrX' : r'' ∈ Subgroup.normalizer (X' : Set G) := by
      have h2 := conj_mem_normalizer_map n⁻¹ hrX
      have e1 : n⁻¹ * r' * n⁻¹⁻¹ = r'' := by rw [hr'def]; group
      rwa [e1] at h2
    rcases hr''X X' hX'le hTX' hrX' with h1 | h1
    · left
      rw [← hXX']
      exact Subgroup.map_mono h1
    · right
      rw [← hXX', h1, hTKb]
  have hTnK : T ≤ Subgroup.normalizer (TK : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hSA.trans hCAN ht⟩
  have hTnKb : T ≤ Subgroup.normalizer (TKb : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hSA.trans hCANb ht⟩
  have hTKT : TK ≤ T := inf_le_left
  have hTKbT : TKb ≤ T := inf_le_left
  have hX₁ : TK ⊓ Kb ≤ V := by
    rcases hrX (TK ⊓ Kb) inf_le_left (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hTnK (hTKT ht), hSA.trans hCANb (hTKT ht)⟩)
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨hrN, hCANb hrA⟩) with h1 | h1
    · exact h1
    · exfalso
      have hle : TK ≤ TKb := fun x hx => ⟨hTKT hx, (h1.symm ▸ hx : x ∈ TK ⊓ Kb).2⟩
      have heq : TK = TKb := Subgroup.eq_of_le_of_card_ge hle (by rw [hTK64, hTKb64])
      apply hnV
      have e1 : A ⊓ Kb = A ⊓ TKb := by rw [hTKbdef, ← inf_assoc, inf_of_le_left hAT]
      have e2 : A ⊓ TK = V := by rw [hTKdef, ← inf_assoc, inf_of_le_left hAT]
      rw [← hVb, e1, ← heq, e2]
  have hcomm₀ : ∀ u ∈ TK, ∀ w ∈ TKb, u * w * u⁻¹ * w⁻¹ ∈ V ⊓ Vb := by
    intro u hu w hw
    have h1 : u * w * u⁻¹ * w⁻¹ ∈ TK := by
      have := (Subgroup.mem_normalizer_iff.mp (hTnK (hTKbT hw)) u⁻¹).mp (TK.inv_mem hu)
      have e : u * w * u⁻¹ * w⁻¹ = u * (w * u⁻¹ * w⁻¹) := by group
      rw [e]
      exact TK.mul_mem hu this
    have h2 : u * w * u⁻¹ * w⁻¹ ∈ TKb :=
      TKb.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTnKb (hTKT hu)) w).mp hw) (TKb.inv_mem hw)
    have h3 : u * w * u⁻¹ * w⁻¹ ∈ V := hX₁ ⟨h1, h2.2⟩
    exact ⟨h3, hVb ▸ ⟨hVA h3, h2.2⟩⟩
  have hclaim2 : ∀ s ∈ TKb, s ∈ TK ⊔ Subgroup.centralizer (K : Set G) := by
    intro s hs
    refine mem_sup_centralizer_of_bender hKq hQ P hPmap hmapV (hSA.trans hCAN (hTKbT hs))
      (hTnK (hTKbT hs)) (hSA.trans hCAV (hTKbT hs)) ?_
    intro t ht
    have := (hcomm₀ t⁻¹ (TK.inv_mem ht) s⁻¹ (TKb.inv_mem hs)).1
    simpa [mul_assoc] using this
  have hNC : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (K : Set G) : Set G) :=
    GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup K
  set Y := TKb ⊓ Subgroup.centralizer (K : Set G) with hYdef
  have hY2 : Nat.card Y ≤ 2 := by
    rcases hr'X Y inf_le_left (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hTnKb (hTKbT ht), hNC (hSA.trans hCAN (hTKbT ht))⟩)
        (Subgroup.inf_normalizer_le_normalizer_inf ⟨hr'N, hNC (hCAN hr'A)⟩) with h1 | h1
    · have hle : Y ≤ CA := fun x hx => ⟨(hVb ▸ h1 hx : x ∈ A ⊓ Kb).1, hx.2⟩
      exact hC2 ▸ Subgroup.card_le_of_le hle
    · exfalso
      have hVbC : Vb ≤ CA := by
        intro x hx
        have hx' : x ∈ A ⊓ Kb := hVb ▸ hx
        have hxY : x ∈ Y := by rw [h1]; exact ⟨hAT hx'.1, hx'.2⟩
        exact ⟨hx'.1, hxY.2⟩
      have := Subgroup.card_le_of_le hVbC
      rw [hV4b, hC2] at this
      omega
  set CT := T ⊓ Subgroup.centralizer (K : Set G) with hCTdef
  have hCTn : T ≤ Subgroup.normalizer (CT : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hNC (hSA.trans hCAN ht)⟩
  set Zb := TK ⊓ (TKb ⊔ CT) with hZbdef
  have h1 := CFSG.Walter.W67.Sec52.card_sup_mul_card_inf (A := CT) (C := TKb) (hTKbT.trans hCTn)
  have h2 := CFSG.Walter.W67.Sec52.card_sup_mul_card_inf (A := CT) (C := Zb)
    ((inf_le_left.trans hTKT).trans hCTn)
  have hCTZb : CT ⊓ Zb = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hx.1.1⟩
    exact hX2 x hx.2.1.2 hx.1.2 k (by simpa using congrArg Subtype.val hk)
  rw [hCTZb, Subgroup.card_bot, mul_one] at h2
  have hCTTKb : CT ⊓ TKb = Y := by
    ext x
    simp only [hCTdef, hYdef, hTKbdef, Subgroup.mem_inf]
    tauto
  rw [hCTTKb] at h1
  have hsub : TKb ⊔ CT ≤ Zb ⊔ CT := by
    refine sup_le (fun s hs => ?_) le_sup_right
    have hset : ((TK ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) =
        (TK : Set G) * (Subgroup.centralizer (K : Set G) : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left TK _
        ((Subgroup.centralizer_le inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
    have hs3 : s ∈ ((TK ⊔ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
      hclaim2 s hs
    rw [hset] at hs3
    obtain ⟨t, ht, c, hc, htc⟩ := Set.mem_mul.mp hs3
    have hcT : c ∈ T := by
      have := T.mul_mem (T.inv_mem (hTKT ht)) (hTKbT hs)
      rwa [← htc, inv_mul_cancel_left] at this
    have hcCT : c ∈ CT := ⟨hcT, hc⟩
    have htZb : t ∈ Zb := by
      refine ⟨ht, ?_⟩
      have := (TKb ⊔ CT).mul_mem (Subgroup.mem_sup_left hs) (Subgroup.mem_sup_right
        (CT.inv_mem hcCT))
      rwa [← htc, mul_inv_cancel_right] at this
    rw [← htc]
    exact (Zb ⊔ CT).mul_mem (Subgroup.mem_sup_left htZb) (Subgroup.mem_sup_right hcCT)
  have hcardle := Subgroup.card_le_of_le hsub
  have hCTpos : 0 < Nat.card CT := Nat.card_pos
  have hZb32 : 32 ≤ Nat.card Zb := by
    rw [hTKb64] at h1
    have e1 : Nat.card CT * 64 ≤ Nat.card (TKb ⊔ CT : Subgroup G) * 2 := by
      rw [← h1]
      exact Nat.mul_le_mul_left _ hY2
    have e2 : Nat.card (TKb ⊔ CT : Subgroup G) * 2 ≤ Nat.card CT * (Nat.card Zb * 2) := by
      rw [← mul_assoc, ← h2]
      exact Nat.mul_le_mul_right _ hcardle
    have e3 := Nat.le_of_mul_le_mul_left (e1.trans e2) hCTpos
    omega
  have hZ1 : ∀ t ∈ Zb, ∀ u ∈ TK, u * t * u⁻¹ * t⁻¹ ∈ V ⊓ Vb := by
    intro t ht u hu
    have hset : ((TKb ⊔ CT : Subgroup G) : Set G) = (TKb : Set G) * (CT : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left TKb CT (inf_le_left.trans hTnKb)
    have ht' : t ∈ ((TKb ⊔ CT : Subgroup G) : Set G) := ht.2
    rw [hset] at ht'
    obtain ⟨s, hs, c, hc, rfl⟩ := Set.mem_mul.mp ht'
    have hcu : c * u⁻¹ = u⁻¹ * c :=
      (Subgroup.mem_centralizer_iff.mp hc.2 u⁻¹ (K.inv_mem hu.2)).symm
    have e : u * (s * c) * u⁻¹ * (s * c)⁻¹ = u * s * u⁻¹ * s⁻¹ := by
      calc u * (s * c) * u⁻¹ * (s * c)⁻¹ = u * s * (c * u⁻¹) * c⁻¹ * s⁻¹ := by group
        _ = u * s * (u⁻¹ * c) * c⁻¹ * s⁻¹ := by rw [hcu]
        _ = u * s * u⁻¹ * s⁻¹ := by group
    rw [e]
    exact hcomm₀ u hu s hs
  have hZbTK : Zb ≤ TK := inf_le_left
  have hidx : (Zb.subgroupOf TK).index ≤ 2 := by
    have h3 := Subgroup.relIndex_mul_card Zb TK
    rw [inf_of_le_left hZbTK, hTK64] at h3
    have h4 : Zb.relIndex TK * 32 ≤ 64 := by
      rw [← h3]
      exact Nat.mul_le_mul_left _ hZb32
    change Zb.relIndex TK ≤ 2
    omega
  have hcommTK : ⁅TK, TK⁆ ≤ V ⊓ Vb := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    by_cases hyZ : y ∈ Zb
    · exact hZ1 y hyZ x hx
    by_cases hxZ : x ∈ Zb
    · have := hZ1 x hxZ y hy
      have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]
      exact (V ⊓ Vb).inv_mem this
    have hidx2 : (Zb.subgroupOf TK).index = 2 := by
      have hne1 : (Zb.subgroupOf TK).index ≠ 1 := by
        intro h1
        rw [Subgroup.index_eq_one] at h1
        apply hxZ
        have : (⟨x, hx⟩ : TK) ∈ Zb.subgroupOf TK := by rw [h1]; exact Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      have hne0 : (Zb.subgroupOf TK).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have hmem : (⟨x, hx⟩ : TK) * (⟨y, hy⟩ : TK)⁻¹ ∈ Zb.subgroupOf TK := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx2, Subgroup.inv_mem_iff,
        Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false hxZ hyZ
    have hz : x * y⁻¹ ∈ Zb := by simpa using Subgroup.mem_subgroupOf.mp hmem
    have := hZ1 (x * y⁻¹) hz y hy
    have e : x * y * x⁻¹ * y⁻¹ = (y * (x * y⁻¹) * y⁻¹ * (x * y⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact (V ⊓ Vb).inv_mem this
  have hVle : V ≤ Vb := (hVcomm.trans hcommTK).trans inf_le_right
  exact hnV (Subgroup.eq_of_le_of_card_ge hVle (by rw [hV4, hV4b])).symm

end Main

end G76

end CFSG.Goldschmidt
