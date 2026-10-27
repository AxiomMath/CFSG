module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.Input20_1Proof
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineTB
public import CFSG.HardMathSupport.Solomon.Proving.LBBalanceUp
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b

public section


namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313i

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G]

theorem exists_mul_of_mem_sup_of_le_normalizer {H N : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ H ⊔ N) :
    ∃ h ∈ H, ∃ n ∈ N, x = h * n := by
  let T : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ n ∈ N, x = h * n}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, n₁, hn₁, rfl⟩ ⟨h₂, hh₂, n₂, hn₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, (h₂⁻¹ * n₁ * h₂) * n₂, N.mul_mem ?_ hn₂, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hH (H.inv_mem hh₂)) n₁).1 hn₁
        simpa using this
      one_mem' := ⟨1, H.one_mem, 1, N.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, n, hn, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, h * n⁻¹ * h⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hH hh) n⁻¹).1 (N.inv_mem hn)
        simpa using this }
  have hHT : H ≤ T := fun h hh => ⟨h, hh, 1, N.one_mem, by simp⟩
  have hNT : N ≤ T := fun n hn => ⟨1, H.one_mem, n, hn, by simp⟩
  exact (sup_le hHT hNT : H ⊔ N ≤ T) hx

theorem conj_mem_core {p : ℕ} {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {o : G} (ho : o ∈ GLAPPrimeCoreOf p K) : g * o * g⁻¹ ∈ GLAPPrimeCoreOf p K := by
  have h1 : GLBConj g K = K := mem_normalizer_iff_gLBConj_eq.1 hg
  have h2 := Lemma1313.glaPPrimeCoreOf_gLBConj_eq (p := p) h1
  have : o ∈ GLBConj g (GLAPPrimeCoreOf p K) := by rw [h2]; exact ho
  exact mem_gLBConj.1 this

@[expose] def actTriv (p : ℕ) (K : Subgroup G) : Subgroup G where
  carrier := {c | c ∈ Subgroup.normalizer (K : Set G) ∧
    ∀ x ∈ K, c * x * c⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p K}
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro c₁ c₂ ⟨hn₁, h₁⟩ ⟨hn₂, h₂⟩
    refine ⟨Subgroup.mul_mem _ hn₁ hn₂, fun x hx => ?_⟩
    have e : c₁ * c₂ * x * (c₁ * c₂)⁻¹ * x⁻¹ =
        (c₁ * (c₂ * x * c₂⁻¹ * x⁻¹) * c₁⁻¹) * (c₁ * x * c₁⁻¹ * x⁻¹) := by group
    rw [e]
    exact (GLAPPrimeCoreOf p K).mul_mem (conj_mem_core hn₁ (h₂ x hx)) (h₁ x hx)
  inv_mem' := by
    rintro c ⟨hn, h⟩
    refine ⟨Subgroup.inv_mem _ hn, fun x hx => ?_⟩
    have hy : c⁻¹ * x * c⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) x).1 hx
    have h1 := h _ hy
    have h2 : (c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹ * (c⁻¹ * x * c⁻¹⁻¹)⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p K :=
      (GLAPPrimeCoreOf p K).inv_mem h1
    have e2 : (c * (c⁻¹ * x * c⁻¹⁻¹) * c⁻¹ * (c⁻¹ * x * c⁻¹⁻¹)⁻¹)⁻¹ = c⁻¹ * x * c * x⁻¹ := by group
    rw [e2] at h2
    simpa using h2

theorem conj_mem_actTriv {p : ℕ} {K : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hc : c ∈ actTriv p K) :
    g * c * g⁻¹ ∈ actTriv p K := by
  obtain ⟨hcn, hc⟩ := hc
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcn) (Subgroup.inv_mem _ hg), fun x hx => ?_⟩
  have hy : g⁻¹ * x * g⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) x).1 hx
  have h1 := conj_mem_core (p := p) hg (hc _ hy)
  have e : g * (c * (g⁻¹ * x * g⁻¹⁻¹) * c⁻¹ * (g⁻¹ * x * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * c * g⁻¹ * x * (g * c * g⁻¹)⁻¹ * x⁻¹ := by group
  rw [e] at h1
  exact h1

theorem gen_aux {p : ℕ} [Fact p.Prime] {M K T₁ : Subgroup G} {b : G}
    (hbord : orderOf b = p) (hKM : IsSubnormal K M) (hbK : b ∈ actTriv p K)
    (hT1p : Nat.Coprime p (Nat.card T₁)) (hT1K : T₁ ≤ Subgroup.normalizer (K : Set G))
    (hbT : b ∈ Subgroup.normalizer (T₁ : Set G))
    (hT1gen : K ≤ ⁅K, T₁⁆ ⊔ GLAPPrimeCoreOf p K) :
    K ⊓ Subgroup.centralizer ({b} : Set G) ≤
      ⨆ x ∈ K ⊓ Subgroup.centralizer ({b} : Set G),
        GLBConj x ((T₁ ⊓ Subgroup.centralizer ({b} : Set G)) ⊔
          (GLAPPrimeCoreOf p M ⊓ Subgroup.centralizer ({b} : Set G))) := by
  have hp : p.Prime := Fact.out
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set O := GLAPPrimeCoreOf p K with hO
  set X := K ⊓ C with hX
  set S := T₁ ⊓ C with hS
  set P₁ := GLAPPrimeCoreOf p M ⊓ C with hP₁
  set W := ⨆ x ∈ X, GLBConj x (S ⊔ P₁) with hW
  have hbN : b ∈ Subgroup.normalizer (K : Set G) := hbK.1
  have hcover := Lemma1313.cover_centralizer hbord (mem_normalizer_iff_gLBConj_eq.1 hbN) hbK.2
  have hOK : O ≤ K := Lemma1313.glaPPrimeCoreOf_le_self K
  have hOM : O ≤ GLAPPrimeCoreOf p M := glaPPrimeCoreOf_le_of_isSubnormal hp hKM
  have hKN : ∀ k ∈ K, k ∈ Subgroup.normalizer (O : Set G) := fun k hk =>
    Lemma1313.mem_normalizer_glaPPrimeCoreOf hk
  have hd : IsPGroup p (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbord, pow_one])
  set V₀ : Subgroup G := T₁ ⊓ actTriv p K with hV₀
  have hV₀p : ¬ p ∣ Nat.card V₀ :=
    (Nat.Prime.coprime_iff_not_dvd hp).1
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hT1p)
  have hnormV : ∀ g ∈ Subgroup.normalizer (K : Set G), g ∈ Subgroup.normalizer (T₁ : Set G) →
      g ∈ Subgroup.normalizer (V₀ : Set G) := by
    intro g hgK hgT
    have key : ∀ g' ∈ Subgroup.normalizer (K : Set G), g' ∈ Subgroup.normalizer (T₁ : Set G) →
        ∀ v ∈ V₀, g' * v * g'⁻¹ ∈ V₀ := by
      intro g' hg'K hg'T v hv
      exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hg'T v).1 hv.1,
        conj_mem_actTriv hg'K hv.2⟩
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · exact key g hgK hgT v
    · intro h
      have := key g⁻¹ (Subgroup.inv_mem _ hgK) (Subgroup.inv_mem _ hgT) _ h
      have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
      rwa [e] at this
  have hdec : ∀ t ∈ T₁, ∃ s ∈ S, ∃ v ∈ V₀, t = s * v := by
    intro t ht
    have htK : t ∈ Subgroup.normalizer (K : Set G) := hT1K ht
    have hbt : b * t * b⁻¹ * t⁻¹ ∈ V₀ := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · exact T₁.mul_mem ((Subgroup.mem_normalizer_iff.1 hbT t).1 ht) (T₁.inv_mem ht)
      · have h1 : t * b⁻¹ * t⁻¹ ∈ actTriv p K :=
          conj_mem_actTriv htK ((actTriv p K).inv_mem hbK)
        have := (actTriv p K).mul_mem hbK h1
        simpa [mul_assoc] using this
    obtain ⟨v, hv, hfix⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_mul_mem_centralizer (p := p)
      (d := b) (x := t) (V := V₀) hd hV₀p (hnormV b hbN hbT)
      (hnormV t htK (Subgroup.le_normalizer ht)) hbt
    exact ⟨t * v, Subgroup.mem_inf.2 ⟨T₁.mul_mem ht hv.1, hfix⟩, v⁻¹, V₀.inv_mem hv, by group⟩
  set Z := ⁅X, S⁆ with hZ
  have hZX : Z ≤ X := by
    refine Subgroup.commutator_le.2 fun y hy s hs => ?_
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hsK : s ∈ Subgroup.normalizer (K : Set G) := hT1K hs.1
      have h1 : s * y⁻¹ * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hsK y⁻¹).1 (K.inv_mem hy.1)
      have e : ⁅y, s⁆ = y * (s * y⁻¹ * s⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact K.mul_mem hy.1 h1
    · exact C.mul_mem (C.mul_mem (C.mul_mem hy.2 hs.2) (C.inv_mem hy.2)) (C.inv_mem hs.2)
  have hcomm : ∀ k ∈ K, ∀ t ∈ T₁, ⁅k, t⁆ ∈ Z ⊔ O := by
    intro k hk t ht
    obtain ⟨y, hy, n, hn, rfl⟩ := hcover k hk
    obtain ⟨s, hs, v, hv, rfl⟩ := hdec t ht
    have hsK : s ∈ Subgroup.normalizer (K : Set G) := hT1K hs.1
    have htK : s * v ∈ Subgroup.normalizer (K : Set G) := hT1K ht
    have hyK : y ∈ K := (Subgroup.mem_inf.1 hy).1
    have hyN : y ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hyK
    have e : ⁅y * n, s * v⁆ = (y * ⁅n, s * v⁆ * y⁻¹) * ⁅y, s⁆ * (s * ⁅y, v⁆ * s⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    have hO1 : y * ⁅n, s * v⁆ * y⁻¹ ∈ O := by
      refine conj_mem_core hyN ?_
      have e1 : ⁅n, s * v⁆ = n * ((s * v) * n⁻¹ * (s * v)⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact O.mul_mem hn (conj_mem_core htK (O.inv_mem hn))
    have hO2 : s * ⁅y, v⁆ * s⁻¹ ∈ O := by
      refine conj_mem_core hsK ?_
      have h1 := hv.2.2 y⁻¹ (K.inv_mem hyK)
      have e1 : ⁅y, v⁆ = y * (v * y⁻¹ * v⁻¹ * y⁻¹⁻¹) * y⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e1]
      exact conj_mem_core hyN h1
    have hyc : ⁅y, s⁆ ∈ Z := Subgroup.commutator_mem_commutator hy hs
    exact (Z ⊔ O).mul_mem ((Z ⊔ O).mul_mem ((le_sup_right : O ≤ Z ⊔ O) hO1) ((le_sup_left : Z ≤ Z ⊔ O) hyc)) ((le_sup_right : O ≤ Z ⊔ O) hO2)
  have hKH : K ≤ Z ⊔ O := by
    refine hT1gen.trans (sup_le ?_ le_sup_right)
    exact Subgroup.commutator_le.2 fun k hk t ht => hcomm k hk t ht
  have hone : S ⊔ P₁ ≤ W := by
    have := (le_iSup₂_of_le (1 : G) (X.one_mem) (le_of_eq (gLBConj_one (S ⊔ P₁)).symm) :
      S ⊔ P₁ ≤ W)
    exact this
  have hZW : Z ≤ W := by
    refine Subgroup.commutator_le.2 fun y hy s hs => ?_
    have h1 : y * s * y⁻¹ ∈ W := by
      have hmem : y * s * y⁻¹ ∈ GLBConj y⁻¹ (S ⊔ P₁) := by
        rw [mem_gLBConj]
        have e : y⁻¹ * (y * s * y⁻¹) * y⁻¹⁻¹ = s := by group
        rw [e]
        exact (le_sup_left : S ≤ S ⊔ P₁) hs
      exact (le_iSup₂_of_le y⁻¹ (X.inv_mem hy) le_rfl : GLBConj y⁻¹ (S ⊔ P₁) ≤ W) hmem
    have h2 : s⁻¹ ∈ W := hone ((le_sup_left : S ≤ S ⊔ P₁) (S.inv_mem hs))
    have e : ⁅y, s⁆ = (y * s * y⁻¹) * s⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact W.mul_mem h1 h2
  intro x hx
  have hxK : x ∈ K := hx.1
  obtain ⟨z, hz, o, ho, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer (H := Z) (N := O)
    (fun z hz => hKN z (hZX hz).1) (hKH hxK)
  have hzC : z ∈ C := (hZX hz).2
  have hoC : o ∈ C := by
    have := C.mul_mem (C.inv_mem hzC) hx.2
    simpa using this
  have hoW : o ∈ W := hone ((le_sup_right : P₁ ≤ S ⊔ P₁) (Subgroup.mem_inf.2 ⟨hOM ho, hoC⟩))
  exact W.mul_mem (hZW hz) hoW

end Gen

section Balance

variable {G : Type} [Group G] [Finite G]

theorem isSubnormal_sSup_of_forall' {X : Subgroup G} (S : Set (Subgroup G))
    (hS : ∀ K ∈ S, K ≤ X ∧ IsSubnormal K X) : IsSubnormal (sSup S) X := by
  have hle : sSup S ≤ X := sSup_le fun K hK => (hS K hK).1
  rw [CFSG.Quasithin.isSubnormal_iff_subgroupOf hle]
  set 𝒮 : Set (Subgroup ↥X) := (fun K : Subgroup G => K.subgroupOf X) '' S with h𝒮
  have h1 : ∀ A ∈ 𝒮, A.IsSubnormal := by
    rintro _ ⟨K, hK, rfl⟩
    exact (CFSG.Quasithin.isSubnormal_iff_subgroupOf (hS K hK).1).1 (hS K hK).2
  have h2 := (CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮 h1).1
  have h3 : (sSup S).subgroupOf X = Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥X)) := by
    have hc : Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥X)) = sSup 𝒮 := by
      refine le_antisymm ((Subgroup.closure_le _).2 (Set.iUnion₂_subset fun A hA => ?_)) ?_
      · exact (le_sSup hA : A ≤ sSup 𝒮)
      · exact sSup_le fun A hA x hx => Subgroup.subset_closure (Set.mem_biUnion hA hx)
    rw [hc]
    refine le_antisymm ?_ (sSup_le ?_)
    · have h4 : sSup S ≤ (sSup 𝒮).map X.subtype := by
        refine sSup_le fun K hK => ?_
        rw [← Subgroup.map_subgroupOf_eq_of_le (hS K hK).1]
        exact Subgroup.map_mono (le_sSup ⟨K, hK, rfl⟩)
      have := Subgroup.comap_mono (f := X.subtype) h4
      rwa [Subgroup.comap_map_eq_self_of_injective X.subtype_injective] at this
    · rintro _ ⟨K, hK, rfl⟩
      exact Subgroup.comap_mono (le_sSup hK)
  rwa [h3]

theorem centralizer_pair_eq (b d : G) :
    Subgroup.centralizer ({b, d} : Set G) =
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({d} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

end Balance

section LayerComponent

variable {G : Type} [Group G] [Finite G]

theorem glaPComponent_layer_inf_cent {p : ℕ} [Fact p.Prime] {L0 : Subgroup G} {b : G}
    (hbord : orderOf b = p) (hnorm : GLBConj b L0 = L0)
    (hcomm : ∀ x ∈ L0, b * x * b⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p L0)
    (hquasi : CFSG.Open.IsQuasisimple (barOf p L0)) :
    GLAPComponent p (L0 ⊓ Subgroup.centralizer ({b} : Set G))
        (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) ∧
      ∀ J : Subgroup G, GLAPComponent p (L0 ⊓ Subgroup.centralizer ({b} : Set G)) J →
        J = GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G)) := by
  classical
  set Y : Subgroup G := L0 ⊓ Subgroup.centralizer ({b} : Set G) with hYdef
  have hYL0 : Y ≤ L0 := inf_le_left
  let f : ↥Y →* (↥L0 ⧸ GLAPPrimeCore p ↥L0) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥L0)).comp (Subgroup.inclusion hYL0)
  have hcov := Lemma1313.cover_centralizer hbord hnorm hcomm
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hyY, n, hn, hxyn⟩ := hcov (x : G) x.2
    refine ⟨⟨y, hyY⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hYL0 ⟨y, hyY⟩) : ↥L0 ⧸ GLAPPrimeCore p ↥L0) =
      QuotientGroup.mk x
    rw [QuotientGroup.eq]
    have hn' : n ∈ (GLAPPrimeCore p ↥L0).map L0.subtype := hn
    obtain ⟨n', hn'mem, hn'eq⟩ := Subgroup.mem_map.1 hn'
    have key : (Subgroup.inclusion hYL0 ⟨y, hyY⟩ : ↥L0)⁻¹ * x = n' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, Subtype.coe_mk]
      have hn'val : (n' : G) = n := hn'eq
      rw [hxyn, hn'val]
      group
    rw [key]
    exact hn'mem
  have hkerle : f.ker ≤ GLAPPrimeCore p ↥Y := by
    have hcop : Nat.Coprime p (Nat.card ↥f.ker) := by
      have hmap : f.ker.map (Subgroup.inclusion hYL0) ≤ GLAPPrimeCore p ↥L0 := by
        rintro _ ⟨k, hk, rfl⟩
        have hk1 : f k = 1 := hk
        have hk2 : QuotientGroup.mk (Subgroup.inclusion hYL0 k) =
            (1 : ↥L0 ⧸ GLAPPrimeCore p ↥L0) := hk1
        exact (QuotientGroup.eq_one_iff _).1 hk2
      have hcard : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL0)) = Nat.card ↥f.ker :=
        Subgroup.card_map_of_injective (f := Subgroup.inclusion hYL0)
          (Subgroup.inclusion_injective hYL0)
      have hdvd : Nat.card ↥(f.ker.map (Subgroup.inclusion hYL0)) ∣
          Nat.card ↥(GLAPPrimeCore p ↥L0) := Subgroup.card_dvd_of_le hmap
      have h2 := Nat.Coprime.coprime_dvd_right hdvd
        (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥L0))
      rw [hcard] at h2
      exact h2
    exact Lemma1313.le_glaPPrimeCore_of_normal (p := p) ↥Y (K := f.ker) inferInstance hcop
  have hkerge : GLAPPrimeCore p ↥Y ≤ f.ker := by
    intro t ht
    have hTn : (GLAPPrimeCore p ↥Y).Normal := inferInstance
    have hmapN : ((GLAPPrimeCore p ↥Y).map f).Normal := hTn.map f hsurj
    have hcop : Nat.Coprime p (Nat.card ↥((GLAPPrimeCore p ↥Y).map f)) := by
      have hdvd := Subgroup.card_map_dvd (GLAPPrimeCore p ↥Y) f
      exact Nat.Coprime.coprime_dvd_right hdvd (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥Y))
    have hle := Lemma1313.le_glaPPrimeCore_of_normal (p := p) (↥L0 ⧸ GLAPPrimeCore p ↥L0) hmapN hcop
    rw [Lemma1311.glaPPrimeCore_quot_eq_bot p ↥L0] at hle
    have hft : f t ∈ (GLAPPrimeCore p ↥Y).map f := Subgroup.mem_map_of_mem f ht
    exact (Subgroup.mem_bot).1 (hle hft)
  have hker : GLAPPrimeCore p ↥Y = f.ker := le_antisymm hkerge hkerle
  let e1 : (↥Y ⧸ GLAPPrimeCore p ↥Y) ≃* (↥L0 ⧸ GLAPPrimeCore p ↥L0) :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  have hYq : CFSG.Open.IsQuasisimple (↥Y ⧸ GLAPPrimeCore p ↥Y) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e1.symm hquasi
  have hYqTop : CFSG.Open.IsQuasisimple (↥(⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y))) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv
      (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)) ≃*
        (↥Y ⧸ GLAPPrimeCore p ↥Y)).symm hYq
  obtain ⟨K, hKc, hKtop⟩ := exists_glaPComponent_barX_eq (p := p) Y
    (K := (⊤ : Subgroup (↥Y ⧸ GLAPPrimeCore p ↥Y)))
    ⟨le_top, CFSG.Open.IsSubnormal.refl ⊤, hYqTop⟩
  have huniq : ∀ J : Subgroup G, GLAPComponent p Y J → J = K := by
    intro J hJ
    have hc : CFSG.Open.IsComponentOf (barX p Y J) ⊤ := hJ.2.2.1
    have htop : barX p Y J = ⊤ := Lemma1313.eq_top_of_isComponentOf_quasisimple hYq hc
    exact glaPComponent_unique hJ hKc (htop.trans hKtop.symm)
  have hlayer : GLAPLayer p Y = K := by
    have hset : {L : Subgroup G | GLAPComponent p Y L} = {K} := by
      ext L
      constructor
      · intro hL
        exact huniq L hL
      · intro hL
        rw [Set.mem_singleton_iff] at hL
        rw [hL]
        exact hKc
    unfold GLAPLayer
    show sSup {L : Subgroup G | GLAPComponent p Y L} = K
    rw [hset, sSup_singleton]
  rw [hlayer]
  exact ⟨hKc, huniq⟩

end LayerComponent

section Tools

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem bmono (p : ℕ) {X S T : Subgroup G} (h : S ≤ T) : barX p X S ≤ barX p X T :=
  CFSG.LocalAnalysis.GLTheoremB.barX_mono p h

theorem le_normalizer_of_input11_6_cop (i11 : Input11_6) (hK : CFSG.Open.IsKProper G)
    (hp : p.Prime) (hp2 : p ≠ 2) {C B X L : Subgroup G}
    (hCtop : C ≠ ⊤) (hBC : B ≤ C) (hXC : X ≤ C) (hSC : IsSCp p ⊤ B)
    (hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C))
    (hX : Nat.Coprime p (Nat.card X))
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hL : GLAPComponent p C L) :
    X ≤ Subgroup.normalizer (L : Set G) := by
  have hKC : CFSG.Open.IsKGroup ↥C := isKGroup_of_isKProper hK hCtop
  have hSC' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf hSC hBC
  have hcop : Nat.Coprime p (Nat.card (X.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]
    exact hX
  have hnorm : B.subgroupOf C ≤ Subgroup.normalizer ((X.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.1 (hBX ((Subgroup.mem_subgroupOf).1 hb)) (x : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hmain := i11 ↥C hKC p hp hp2 (B.subgroupOf C) hSC' hrank (X.subgroupOf C) hcop hnorm
    (L.subgroupOf C) (glaPComponent_top hL)
  intro x hx
  have hxX : (⟨x, hXC hx⟩ : ↥C) ∈ X.subgroupOf C := (Subgroup.mem_subgroupOf).2 hx
  have hxn := Subgroup.mem_normalizer_iff.1 (hmain hxX)
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := (hxn ⟨y, hL.1 hy⟩).1 ((Subgroup.mem_subgroupOf).2 hy)
    exact (Subgroup.mem_subgroupOf).1 (by simpa using h1)
  · intro hy
    have hyC : y ∈ C := by
      have : x * y * x⁻¹ ∈ C := hL.1 hy
      have := C.mul_mem (C.mul_mem (C.inv_mem (hXC hx)) this) (hXC hx)
      simpa [mul_assoc] using this
    have h1 := (hxn ⟨y, hyC⟩).2 ((Subgroup.mem_subgroupOf).2 (by simpa using hy))
    exact (Subgroup.mem_subgroupOf).1 h1

theorem rank_le_of_bOneMax (hSt : GLStanding G m p) {B : Subgroup G} (hB : IsBOneMax p B)
    {C : Subgroup G} (hBC : B ≤ C) :
    GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C) := by
  have hp := hSt.prime
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf (lemma23_proved G m p hSt B hB) hBC
  refine (glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_
  rw [hSt.rank_eq]
  refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'.2.1 ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hSt.card_eq hB]

theorem barX_cop_props (i11 : Input11_6) (hSt : GLStanding G m p) {B : Subgroup G}
    (hB : IsBOneMax p B) {C S : Subgroup G} (hCtop : C ≠ ⊤) (hBC : B ≤ C) (hSC : S ≤ C)
    (hSp : Nat.Coprime p (Nat.card S)) (hBS : B ≤ Subgroup.normalizer (S : Set G)) :
    barX p C S ≤ Subgroup.centralizer
        ((CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) :
          Set (↥C ⧸ GLAPPrimeCore p ↥C)) ∧
      ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
        barX p C S ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf (lemma23_proved G m p hSt B hB) hBC
  have hBbar : IsSCp p ⊤ (barX p C B) :=
    isSCp_map_quotient (GLAPPrimeCore p ↥C)
      ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hB'
  have hXb : Nat.Coprime p (Nat.card (barX p C S)) := by
    have hdvd := Subgroup.card_map_dvd (S.subgroupOf C) (QuotientGroup.mk' (GLAPPrimeCore p ↥C))
    have hcard : Nat.card (S.subgroupOf C) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
    rw [hcard] at hdvd
    exact Nat.Coprime.coprime_dvd_right hdvd hSp
  have hBXb : barX p C B ≤ Subgroup.normalizer (barX p C S : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    barX_le_normalizer hBS
  have h1 := CFSG.HardMathSupport.Dickson.I271.centralizes_pCore_of_isSCp_coprime input20_1_proved
    hp hp2 hBbar hXb hBXb
  refine ⟨h1, fun K hK => ?_⟩
  obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq C hK
  exact barX_le_normalizer (le_normalizer_of_input11_6_cop i11 hSt.kProper hp hp2 hCtop hBC hSC
    (lemma23_proved G m p hSt B hB) (rank_le_of_bOneMax hSt hB hBC) hSp hBS hL)

theorem glaPComponent_up {p : ℕ} (hp : p.Prime) {T H K : Subgroup G}
    (hK : GLAPComponent p H K) (hHT : IsSubnormal H T) : GLAPComponent p T K := by
  obtain ⟨hKH, hsnKH, hcompH, hminH⟩ := hK
  have hHT' : H ≤ T := isSubnormal_le' hHT
  have hKT : IsSubnormal K T := isSubnormal_trans' hsnKH hHT
  have hKT' : K ≤ T := hKH.trans hHT'
  have hcore : H ⊓ GLAPPrimeCoreOf p T = GLAPPrimeCoreOf p H :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hHT
  have key : ∀ J K' : Subgroup G, J ≤ H → K' ≤ H → barX p T J ≤ barX p T K' →
      barX p H J ≤ barX p H K' := by
    intro J K' hJH hK'H hle
    refine barX_le_of_forall hK'H (fun j hj => ?_)
    obtain ⟨k, hk, hkj⟩ := exists_of_barX_le (X := T) (J := K') (K := J) hle hj (hHT' (hJH hj))
    refine ⟨k, hk, ?_⟩
    rw [← hcore]
    exact ⟨H.mul_mem (H.inv_mem (hK'H hk)) (hJH hj), hkj⟩
  refine ⟨hKT', hKT, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := T) p hKT
    rwa [barX_self] at this
  · have e : ↥(barX p T K) ≃* ↥(barX p H K) :=
      (quotEquivBarX hp hKT' hKT).symm.trans (quotEquivBarX hp hKH hsnKH)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hcompH.2.2
  · intro J hJK hJsnT heq
    have hJH : J ≤ H := hJK.le.trans hKH
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsnT hJH hHT'
    exact hminH J hJK hJsnH (le_antisymm (key J K hJH hKH heq.le) (key K J hKH hJH heq.ge))

theorem glaPComponent_lift {p : ℕ} (hp : p.Prime) {H M K : Subgroup G}
    (hK : GLAPComponent p H K) (hHM : H ≤ M) (hsnM : IsSubnormal K M) :
    GLAPComponent p M K := by
  obtain ⟨hKH, hsnH, hcomp, hmin⟩ := hK
  have hKM : K ≤ M := hKH.trans hHM
  refine ⟨hKM, hsnM, ⟨le_top, ?_, ?_⟩, ?_⟩
  · have := isSubnormal_barX (C := M) p hsnM
    rwa [barX_self] at this
  · have e : ↥(barX p H K) ≃* ↥(barX p M K) :=
      (quotEquivBarX hp hKH hsnH).symm.trans (quotEquivBarX hp hKM hsnM)
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hcomp.2.2
  · intro J hJ hJsn heq
    have hJL : J ≤ K := hJ.le
    have hcoreL : K ⊓ GLAPPrimeCoreOf p M ≤ GLAPPrimeCoreOf p H := by
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsnM]
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hsnH
    have hJsnH : IsSubnormal J H := isSubnormal_of_le_of_le hJsn (hJL.trans hKH) hHM
    refine hmin J hJ hJsnH ?_
    show barX p H J = barX p H K
    refine le_antisymm (bmono p hJL) ?_
    refine barX_le_of_forall (hJL.trans hKH) (fun k hk => ?_)
    obtain ⟨j, hj, hjk⟩ := exists_of_barX_le (X := M) (le_of_eq heq.symm) hk (hKM hk)
    exact ⟨j, hj, hcoreL ⟨K.mul_mem (K.inv_mem (hJL hj)) hk, hjk⟩⟩

end Tools

section Core

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem barX_le_centralizer_of_balanced (i11 : Input11_6) (hSt : GLStanding G m p)
    {B : Subgroup G} (hB : IsBOneMax p B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {S : Subgroup G} (hSC : S ≤ Subgroup.centralizer ({b} : Set G))
    (hSp : Nat.Coprime p (Nat.card S)) (hBS : B ≤ Subgroup.normalizer (S : Set G))
    {L : Subgroup G} (hL : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L)
    (hbal : IsStronglyLocallyOneBalanced p B b L) :
    barX p (Subgroup.centralizer ({b} : Set G)) S ≤
      Subgroup.centralizer ((barX p (Subgroup.centralizer ({b} : Set G)) L :
        Subgroup (↥(Subgroup.centralizer ({b} : Set G)) ⧸
          GLAPPrimeCore p ↥(Subgroup.centralizer ({b} : Set G)))) : Set _) := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have hBC : B ≤ Subgroup.centralizer ({b} : Set G) := le_centralizer_of_mem hB.1.1 hb
  have hCtop : Subgroup.centralizer ({b} : Set G) ≠ ⊤ := centralizer_singleton_ne_top hSt hb1
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_input11_6_cop i11 hSt.kProper hp hp2 hCtop hBC hSC
      (lemma23_proved G m p hSt B hB) (rank_le_of_bOneMax hSt hB hBC) hSp hBS hL
  have hcomm : ⁅L, S⁆ ≤ GLAPPrimeCoreOf p L :=
    hbal S (le_inf hSL hSC) hSp (fun g hg => hBS hg.1)
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have h3 : s * t * s⁻¹ * t⁻¹ ∈ ⁅S, L⁆ := Subgroup.commutator_mem_commutator hs ht
  rw [Subgroup.commutator_comm] at h3
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hcomm h3)

theorem pComponent_of_lambda (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (hSt : GLStanding G m p) {B M : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsPreUniquenessTwoLocal p B M) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {S P X : Subgroup G} (hSC : S ≤ Subgroup.centralizer ({b} : Set G))
    (hSp : Nat.Coprime p (Nat.card S)) (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hPC : P ≤ Subgroup.centralizer ({b} : Set G))
    (hPp : Nat.Coprime p (Nat.card P)) (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hXMC : X ≤ M ⊓ Subgroup.centralizer ({b} : Set G))
    (hgen : barX p (Subgroup.centralizer ({b} : Set G)) X ≤
      ⨆ y ∈ barX p (Subgroup.centralizer ({b} : Set G)) X,
        GLBConj y (barX p (Subgroup.centralizer ({b} : Set G)) S ⊔
          barX p (Subgroup.centralizer ({b} : Set G)) P))
    {J : Subgroup G} (hJ : GLAPComponent p (M ⊓ Subgroup.centralizer ({b} : Set G)) J)
    (hJX : J ≤ X) : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have := hSt.simple
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hSt hb1
  set H₀ := M ⊓ C with hH₀
  have hXC : X ≤ C := hXMC.trans inf_le_right
  have hJC : J ≤ C := hJX.trans hXC
  have hQcore : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hQ : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
    isKGroup_quotient' (isKGroup_of_isKProper hSt.kProper hCtop) _
  have hOut : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    fun K hK => outer_solvable_of_component hSch hQ hK
  obtain ⟨hSF, hSN⟩ := barX_cop_props i11 hSt hB hCtop hBC hSC hSp hBS
  obtain ⟨hPF, hPN⟩ := barX_cop_props i11 hSt hB hCtop hBC hPC hPp hBP
  have hSPN : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      barX p C S ⊔ barX p C P ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    fun K hK => sup_le (hSN K hK) (hPN K hK)
  have hSPF : barX p C S ⊔ barX p C P ≤ Subgroup.centralizer
      (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    sup_le hSF hPF
  have hXN : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      barX p C X ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := fun K hK =>
    le_of_le_iSup_conj (F := fun K' => Subgroup.normalizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_normalizer g K') hgen
      (fun y _ => hSPN _ (isComponentOf_gLBConj hK y⁻¹))
  have : (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C)).Normal :=
    CFSG.LieType.BorelTits.pCore_normal p
  have hXF : barX p C X ≤ Subgroup.centralizer
      (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    le_of_le_iSup_conj
      (F := fun K' => Subgroup.centralizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_centralizer g K') hgen
      (fun y _ => by rw [gLBConj_eq_of_normal]; exact hSPF)
  have hJperf : ⁅J, J⁆ = J := glaPComponent_perfect hJ
  have hJbperf : ⁅barX p C J, barX p C J⁆ = barX p C J := barX_perfect p hJC hJperf
  have hJN : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      barX p C J ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := fun K hK =>
    (bmono p hJX).trans (hXN K hK)
  have hJF : barX p C J ≤ Subgroup.centralizer
      (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    (bmono p hJX).trans hXF
  have hJE : barX p C J ≤ CFSG.ComponentClassification.Layer.subgroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
    le_layer_of_perfect hp hQcore hOut hJbperf hJF hJN
  set 𝒦 : Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) := {K | ∃ L : Subgroup G,
    GLAPComponent p C L ∧ IsStronglyLocallyOneBalanced p B b L ∧ barX p C L = K} with h𝒦
  have h𝒦c : ∀ K ∈ 𝒦, IsComponentOf K ⊤ := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact hL.2.2.1
  have hSPK : ∀ K ∈ 𝒦, barX p C S ⊔ barX p C P ≤
      Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rintro _ ⟨L, hL, hbal, rfl⟩
    exact sup_le (barX_le_centralizer_of_balanced i11 hSt hB hb hb1 hSC hSp hBS hL hbal)
      (barX_le_centralizer_of_balanced i11 hSt hB hb hb1 hPC hPp hBP hL hbal)
  have hXK : ∀ K ∈ 𝒦, barX p C X ≤
      Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    intro K hK
    refine le_of_le_iSup_conj
      (F := fun K' => Subgroup.centralizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_centralizer g K') hgen (fun y hy => ?_)
    have hyn : y⁻¹ ∈ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
      Subgroup.inv_mem _ (hXN K (h𝒦c K hK) hy)
    rw [mem_normalizer_iff_gLBConj_eq.1 hyn]
    exact hSPK K hK
  have hJK : ∀ K ∈ 𝒦, barX p C J ≤
      Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := fun K hK =>
    (bmono p hJX).trans (hXK K hK)
  have hJΛ := le_layer_diff_of_perfect 𝒦 h𝒦c hJbperf hJE hJK
  have hlam : lambdaOf p B b ≤ M := lambdaOf_le_of_isPreUniquenessTwoLocal hM hb hb1
  have hΛ' : (⨆ K ∈ {K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) | IsComponentOf K ⊤ ∧ K ∉ 𝒦}, K) ≤
      barX p C H₀ := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq C hK.1
    have hbal : ¬ IsStronglyLocallyOneBalanced p B b L := fun h => hK.2 ⟨L, hL, h, rfl⟩
    have hLM : L ≤ M := (le_sSup ⟨hL, hbal⟩ : L ≤ lambdaOf p B b).trans hlam
    exact bmono p (le_inf hLM hL.1)
  have hJH₀ : IsSubnormal J H₀ := hJ.2.1
  have hJbar : IsSubnormal (barX p C J) ⊤ :=
    isSubnormal_trans'
      (isSubnormal_of_le_of_le (isSubnormal_barX p hJH₀) hJΛ hΛ')
      (isSubnormal_iSup_components _ (fun K hK => hK.1))
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  set P' : Subgroup G := ((barX p C J).comap π).map C.subtype with hP'
  have hPC' : IsSubnormal P' C := isSubnormal_preimage_barX p hJbar
  have hJP : J ≤ P' := by
    intro j hj
    have hjC : j ∈ C := hJC hj
    exact ⟨⟨j, hjC⟩, ⟨⟨j, hjC⟩, (Subgroup.mem_subgroupOf).2 hj, rfl⟩, rfl⟩
  have hPH₀ : P' ≤ H₀ := by
    rintro _ ⟨c, ⟨c', hc', hcc'⟩, rfl⟩
    have hker : c'⁻¹ * c ∈ GLAPPrimeCore p ↥C := QuotientGroup.eq.1 hcc'
    have hK0M : ((c'⁻¹ * c : ↥C) : G) ∈ M := lemma91_i hSt hB hM hb ⟨_, hker, rfl⟩
    have hc'M : (c' : G) ∈ M := (hXMC (hJX ((Subgroup.mem_subgroupOf).1 hc'))).1
    refine ⟨?_, c.2⟩
    have : (c : G) = (c' : G) * ((c'⁻¹ * c : ↥C) : G) := by simp
    rw [Subgroup.coe_subtype, this]
    exact M.mul_mem hc'M hK0M
  have hJsn : IsSubnormal J C :=
    isSubnormal_trans' (isSubnormal_of_le_of_le hJH₀ hJP hPH₀) hPC'
  exact glaPComponent_lift hp hJ (inf_le_right : H₀ ≤ C) hJsn

end Core

section Block

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem layer_components (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (hSt : GLStanding G m p) {B M : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsPreUniquenessTwoLocal p B M) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    {K : Subgroup G} (hKM : IsSubnormal K M) (hbK : b ∈ actTriv p K)
    {T₁ : Subgroup G} (hT1p : Nat.Coprime p (Nat.card T₁))
    (hT1K : T₁ ≤ Subgroup.normalizer (K : Set G)) (hBT : B ≤ Subgroup.normalizer (T₁ : Set G))
    (hT1gen : K ≤ ⁅K, T₁⁆ ⊔ GLAPPrimeCoreOf p K) :
    ∃ 𝒮 : Set (Subgroup G),
      (∀ J ∈ 𝒮, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) J) ∧
        GLAPLayer p (K ⊓ Subgroup.centralizer ({b} : Set G)) = ⨆ J ∈ 𝒮, J := by
  have hp := hSt.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hbord : orderOf b = p := orderOf_eq_prime (hB.1.1.2 b hb) hb1
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hKC : IsSubnormal (K ⊓ C) (M ⊓ C) := isSubnormal_inf hKM C
  have hXMC : K ⊓ C ≤ M ⊓ C := inf_le_inf_right C hKM.le
  have hXC : K ⊓ C ≤ C := inf_le_right
  refine ⟨{J | GLAPComponent p (K ⊓ C) J}, fun J hJ => ?_, by
    unfold GLAPLayer
    exact sSup_eq_iSup⟩
  have hJ' : GLAPComponent p (M ⊓ C) J := glaPComponent_up hp hJ hKC
  set S := T₁ ⊓ C with hS
  set P := GLAPPrimeCoreOf p M ⊓ C with hP
  have hSC : S ≤ C := inf_le_right
  have hPC : P ≤ C := inf_le_right
  have hSp : Nat.Coprime p (Nat.card S) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hT1p
  have hPp : Nat.Coprime p (Nat.card P) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (Lemma1313.coprime_card_glaPPrimeCoreOf p M)
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := fun g hg =>
    mem_normalizer_inf (hBT hg) (Subgroup.le_normalizer (hBC hg))
  have hBP : B ≤ Subgroup.normalizer (P : Set G) := fun g hg =>
    mem_normalizer_inf (le_normalizer_glaPPrimeCoreOf p M (hBM hg))
      (Subgroup.le_normalizer (hBC hg))
  have hXW := gen_aux (M := M) hbord hKM hbK hT1p hT1K (hBT hb) hT1gen
  have hSPC : S ⊔ P ≤ C := sup_le hSC hPC
  have hle : barX p C (S ⊔ P) ≤ barX p C S ⊔ barX p C P := by
    unfold barX
    rw [Subgroup.subgroupOf_sup hSC hPC, Subgroup.map_sup]
  have hgen : barX p C (K ⊓ C) ≤ ⨆ y ∈ barX p C (K ⊓ C),
      GLBConj y (barX p C S ⊔ barX p C P) :=
    (bmono p hXW).trans ((barX_iSup_conj_le p hXC hSPC).trans
      (iSup₂_mono fun y _ => gLBConj_mono y hle))
  exact pComponent_of_lambda hSch i11 hSt hB hM hb hb1 hSC hSp hBS hPC hPp hBP hXMC hgen hJ' hJ.1

end Block

section BalanceNorm

variable {G : Type} [Group G] [Finite G]

theorem glaPLayer_le_of_comm {p : ℕ} (hp : p.Prime) {X X' : Subgroup G} (hXX' : X ≤ X')
    (hcomm : ∀ a ∈ X', ∀ b ∈ X', ⁅a, b⁆ ∈ X) : GLAPLayer p X' ≤ GLAPLayer p X := by
  unfold GLAPLayer
  refine sSup_le fun J hJ => ?_
  have hJ' : GLAPComponent p X' J := hJ
  have hJX : J ≤ X := by
    rw [← glaPComponent_perfect hJ']
    exact Subgroup.commutator_le.2 fun a ha b hb => hcomm a (hJ'.1 ha) b (hJ'.1 hb)
  exact le_sSup (glaPComponent_of_le hp hJ' hJX hXX')

theorem commutator_mem_of_sup_zpowers {X : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (X : Set G)) {a b : G}
    (ha : a ∈ X ⊔ Subgroup.zpowers d) (hb : b ∈ X ⊔ Subgroup.zpowers d) : ⁅a, b⁆ ∈ X := by
  have hEN : Subgroup.zpowers d ≤ Subgroup.normalizer (X : Set G) := (Subgroup.zpowers_le).2 hdN
  rw [sup_comm] at ha hb
  obtain ⟨e₁, he₁, x₁, hx₁, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hEN ha
  obtain ⟨e₂, he₂, x₂, hx₂, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hEN hb
  have hcomm : e₁ * e₂ = e₂ * e₁ := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 he₁
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 he₂
    exact (Commute.zpow_zpow_self d i j).eq
  have hc2 : e₁⁻¹ * e₂ * e₁ = e₂ := by
    calc e₁⁻¹ * e₂ * e₁ = e₁⁻¹ * (e₂ * e₁) := by group
      _ = e₁⁻¹ * (e₁ * e₂) := by rw [hcomm]
      _ = e₂ := by group
  have hu₁ : e₁ * x₁ * e₁⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hEN he₁) x₁).1 hx₁
  have hu₂ : e₂ * x₂ * e₂⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 (hEN he₂) x₂).1 hx₂
  have hv₂ : e₁ * (e₂ * x₂ * e₂⁻¹) * e₁⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.1 (hEN he₁) _).1 hu₂
  have hv₁ : e₂ * (e₁ * x₁ * e₁⁻¹)⁻¹ * e₂⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.1 (hEN he₂) _).1 (X.inv_mem hu₁)
  have e : ⁅e₁ * x₁, e₂ * x₂⁆ =
      (e₁ * x₁ * e₁⁻¹) * (e₁ * (e₂ * x₂ * e₂⁻¹) * e₁⁻¹) *
        (e₂ * (e₁ * x₁ * e₁⁻¹)⁻¹ * e₂⁻¹) * (e₂ * x₂ * e₂⁻¹)⁻¹ := by
    have h1 : (e₁ * x₁ * e₁⁻¹) * (e₁ * (e₂ * x₂ * e₂⁻¹) * e₁⁻¹) *
        (e₂ * (e₁ * x₁ * e₁⁻¹)⁻¹ * e₂⁻¹) * (e₂ * x₂ * e₂⁻¹)⁻¹ =
        e₁ * x₁ * e₂ * x₂ * e₂⁻¹ * (e₁⁻¹ * e₂ * e₁) * x₁⁻¹ * e₁⁻¹ * x₂⁻¹ * e₂⁻¹ := by group
    rw [h1, hc2]
    simp only [commutatorElement_def]
    group
  rw [e]
  exact X.mul_mem (X.mul_mem (X.mul_mem hu₁ hv₂) hv₁) (X.inv_mem hu₂)

theorem layer_inf_cent_le_of_balance
    (i2 : CFSG.HardMathSupport.Solomon.LocalBalance.Input18_2One) {p : ℕ} (hp : p.Prime)
    (hK : CFSG.Open.IsKProper G) {X : Subgroup G} {d : G}
    (hdE : IsElemAbelian p (Subgroup.zpowers d)) (hdN : d ∈ Subgroup.normalizer (X : Set G))
    (htop : X ⊔ Subgroup.zpowers d ≠ ⊤) :
    GLAPLayer p (X ⊓ Subgroup.centralizer ({d} : Set G)) ≤ GLAPLayer p X := by
  set E := Subgroup.zpowers d with hE
  set X' := X ⊔ E with hX'
  have hX'N : X' ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hdN)
  have hXX' : IsSubnormal X X' :=
    IsSubnormal.step le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hX'N) (IsSubnormal.refl X')
  have hK' : CFSG.Open.IsKGroup ↥X' := isKGroup_of_isKProper hK htop
  have hbal := CFSG.HardMathSupport.Solomon.Proving.glaPLayer_inf_centralizer_le_of_input18_2One i2
    hK' hp (le_sup_right : E ≤ X') hdE
  have hcentE : Subgroup.centralizer (E : Set G) = Subgroup.centralizer ({d} : Set G) := by
    rw [hE, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcentE] at hbal
  have hsn : IsSubnormal (X ⊓ Subgroup.centralizer ({d} : Set G))
      (X' ⊓ Subgroup.centralizer ({d} : Set G)) := isSubnormal_inf hXX' _
  have h1 : GLAPLayer p (X ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      GLAPLayer p (X' ⊓ Subgroup.centralizer ({d} : Set G)) := by
    unfold GLAPLayer
    exact sSup_le fun J hJ => le_sSup (glaPComponent_up hp hJ hsn)
  exact h1.trans (hbal.trans (glaPLayer_le_of_comm hp le_sup_left
    fun a ha b hb => commutator_mem_of_sup_zpowers hdN ha hb))

end BalanceNorm

section Instance

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}

theorem L0_le_istar (h : Cex1310 G m p B M E A D T R L0 d) : L0 ≤ Istar p M D :=
  h.hL0.1.trans ((Lemma1313.piLayer_le_self' p _).trans inf_le_left)

theorem L1_le_istar (h : Cex1310 G m p B M E A D T R L0 d) : L1of p M D L0 ≤ Istar p M D :=
  iSup₂_le fun _ hg => (gLBConj_le_iff_of_mem hg _).2 (L0_le_istar h)

theorem L1_isSubnormal (h : Cex1310 G m p B M E A D T R L0 d) :
    IsSubnormal (L1of p M D L0) M :=
  isSubnormal_trans'
    (IsSubnormal.step (L1_le_istar h)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (L1_le_istar h)).2 fun g hg => by
        rw [mem_normalizer_iff_gLBConj_eq]
        exact Lemma1313.L1of_gLBConj_eq_of_mem_istar hg)
      (IsSubnormal.refl _))
    (istar_isSubnormal p M D)

theorem actTriv_of_centBar {p : ℕ} [Fact p.Prime] {X K : Subgroup G} {b : G}
    (hb : b ∈ centBar p X K) : b ∈ actTriv p K := by
  refine ⟨Lemma1313.mem_normalizer_of_centBar hb, fun x hx => ?_⟩
  have hw := Lemma1313.inv_mul_mem_glaPPrimeCoreOf_of_centBar hb hx
  have hxn := Lemma1313.mem_normalizer_glaPPrimeCoreOf (p := p) hx
  have e : b * x * b⁻¹ * x⁻¹ = x * ((b * x * b⁻¹)⁻¹ * x)⁻¹ * x⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 hxn _).1 ((GLAPPrimeCoreOf p K).inv_mem hw)

theorem lemma1313_i_of_T1 (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) {b : G}
    (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1) {T₁ : Subgroup G}
    (hT1p : Nat.Coprime p (Nat.card T₁))
    (hT1K : T₁ ≤ Subgroup.normalizer (L1of p M D L0 : Set G))
    (hBT : B ≤ Subgroup.normalizer (T₁ : Set G))
    (hT1gen : L1of p M D L0 ≤ ⁅L1of p M D L0, T₁⁆ ⊔ GLAPPrimeCoreOf p (L1of p M D L0)) :
    ∃ S : Set (Subgroup G), (∀ X ∈ S, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) X) ∧
      GLAPLayer p (L1of p M D L0 ⊓ Subgroup.centralizer ({b} : Set G)) = ⨆ X ∈ S, X := by
  haveI : Fact p.Prime := ⟨GLStanding.prime h.standing⟩
  have hbU : b ∈ U := (Subgroup.mem_inf.1 hb).2
  exact layer_components hSch i11 h.standing h.bOne h.pre (hU.1.1 hbU) hb1 (L1_isSubnormal h)
    (actTriv_of_centBar hb) hT1p hT1K hBT hT1gen

end Instance

section CaseA

variable {G : Type} [Group G] [Finite G]

theorem commutator_le_of_central {L T O : Subgroup G} (hLperf : ⁅L, L⁆ = L) (hO : O ≤ L)
    (hLN : L ≤ Subgroup.normalizer (O : Set G)) (hTN : T ≤ Subgroup.normalizer (O : Set G))
    (hcent : ∀ g ∈ ⁅L, T⁆, ∀ x ∈ L, ⁅g, x⁆ ∈ O) : ⁅L, T⁆ ≤ O := by
  set W : Subgroup G := L ⊔ T with hW
  have hLW : L ≤ W := le_sup_left
  have hTW : T ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (O : Set G) := sup_le hLN hTN
  haveI hnorm : (O.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hWN
  let ρ : ↥W →* (↥W ⧸ O.subgroupOf W) := QuotientGroup.mk' (O.subgroupOf W)
  set L' : Subgroup ↥W := L.subgroupOf W with hL'
  set T' : Subgroup ↥W := T.subgroupOf W with hT'
  have hL'perf : ⁅L', L'⁆ = L' := by
    rw [hL', ← subgroupOf_commutator hLW hLW, hLperf]
  have hLbperf : ⁅L'.map ρ, L'.map ρ⁆ = L'.map ρ := by
    rw [← Subgroup.map_commutator, hL'perf]
  have hcomm' : ⁅L', T'⁆ = ⁅L, T⁆.subgroupOf W := (subgroupOf_commutator hLW hTW).symm
  have h1 : ⁅⁅L'.map ρ, T'.map ρ⁆, L'.map ρ⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    refine Subgroup.commutator_le.2 fun g hg x hx => ?_
    rw [hcomm'] at hg
    have hgG : (g : G) ∈ ⁅L, T⁆ := (Subgroup.mem_subgroupOf).1 hg
    have := hcent (g : G) hgG (x : G) ((Subgroup.mem_subgroupOf).1 hx)
    exact (Subgroup.mem_subgroupOf).2 (by simpa [commutatorElement_def] using this)
  have h2 : ⁅⁅T'.map ρ, L'.map ρ⁆, L'.map ρ⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (T'.map ρ) (L'.map ρ)]
    exact h1
  have h3 : ⁅⁅L'.map ρ, L'.map ρ⁆, T'.map ρ⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hLbperf] at h3
  have h4 : ⁅L', T'⁆ ≤ O.subgroupOf W := by
    have : (⁅L', T'⁆).map ρ = ⊥ := by
      rw [Subgroup.map_commutator]
      exact h3
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at this
    exact this
  intro g hg
  have hgW : g ∈ W := commutator_le_of_le' hLW hTW hg
  have : (⟨g, hgW⟩ : ↥W) ∈ ⁅L', T'⁆ := by
    rw [hcomm']
    exact (Subgroup.mem_subgroupOf).2 hg
  exact (Subgroup.mem_subgroupOf).1 (h4 this)

theorem mem_normalizer_core_of_mem_normalizer {p : ℕ} {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact fun hn => conj_mem_core hg hn
  · intro hn
    have := conj_mem_core (Subgroup.inv_mem _ hg) hn
    have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
    rwa [e] at this

theorem le_commutator_sup_core {p : ℕ} (hp : p.Prime) {M L T : Subgroup G} (hLM : IsSubnormal L M)
    (hL : GLAPComponent p L L) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hnc : ¬ barX p M T ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    L ≤ ⁅L, T⁆ ⊔ GLAPPrimeCoreOf p L := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O := GLAPPrimeCoreOf p L with hO
  have hJL : ⁅L, T⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.1 hTL
  have hJn : (⁅L, T⁆.subgroupOf L).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left L T)
  have hQ : CFSG.Open.IsQuasisimple (↥L ⧸ GLAPPrimeCore p ↥L) :=
    Lemma1313.isQuasisimple_barOf_of_pComp hL
  have hN : (barX p L ⁅L, T⁆).Normal :=
    Subgroup.Normal.map hJn _ (QuotientGroup.mk'_surjective _)
  rcases Lemma1313.normal_central_or_top hN hQ with hc | htop
  · exfalso
    apply hnc
    have hOL : O ≤ L := Lemma1313.glaPPrimeCoreOf_le_self L
    have hLperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
    have hLN : L ≤ Subgroup.normalizer (O : Set G) := fun x hx =>
      Lemma1313.mem_normalizer_glaPPrimeCoreOf hx
    have hTN : T ≤ Subgroup.normalizer (O : Set G) := fun t ht =>
      mem_normalizer_core_of_mem_normalizer (hTL ht)
    have hcent : ∀ g ∈ ⁅L, T⁆, ∀ x ∈ L, ⁅g, x⁆ ∈ O := by
      intro g hg x hx
      have hgbar : QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨g, hJL hg⟩ ∈ barX p L ⁅L, T⁆ :=
        ⟨⟨g, hJL hg⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩
      have hz := Subgroup.mem_center_iff.1 (hc hgbar) (QuotientGroup.mk' (GLAPPrimeCore p ↥L) ⟨x, hx⟩)
      have h1 : ⁅(⟨g, hJL hg⟩ : ↥L), (⟨x, hx⟩ : ↥L)⁆ ∈ GLAPPrimeCore p ↥L := by
        rw [← QuotientGroup.ker_mk' (GLAPPrimeCore p ↥L), MonoidHom.mem_ker, map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 hz.symm
      exact ⟨_, h1, by simp [commutatorElement_def]⟩
    have hle : ⁅L, T⁆ ≤ O := commutator_le_of_central hLperf hOL hLN hTN hcent
    refine barX_le_centralizer fun t ht x hx _ _ => ?_
    have h3 : t * x * t⁻¹ * x⁻¹ ∈ ⁅T, L⁆ := Subgroup.commutator_mem_commutator ht hx
    rw [Subgroup.commutator_comm] at h3
    exact glaPPrimeCoreOf_le_of_isSubnormal hp hLM (hle h3)
  · intro x hx
    have hle : barX p L L ≤ barX p L ⁅L, T⁆ := by
      rw [htop, barX_self]
    obtain ⟨j, hj, hjx⟩ := exists_of_barX_le hle hx hx
    have e : x = j * (j⁻¹ * x) := by group
    rw [e]
    exact (⁅L, T⁆ ⊔ O).mul_mem ((le_sup_left : ⁅L, T⁆ ≤ ⁅L, T⁆ ⊔ O) hj)
      ((le_sup_right : O ≤ ⁅L, T⁆ ⊔ O) hjx)


theorem istar_component_self_of_a {p : ℕ} {M D : Subgroup G} (h139a : Prop139a p M D) :
    GLAPComponent p (Istar p M D) (Istar p M D) := by
  obtain ⟨-, hIeq, L, hLc, hIL, -, -⟩ := h139a
  have hIs : Istar p M D = L := hIeq.symm.trans hIL
  rw [hIL] at hLc
  rw [hIs]
  exact hLc

theorem L1_eq_istar_of_a {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) :
    L1of p M D L0 = Istar p M D := by
  have hp : p.Prime := GLStanding.prime h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hI : GLAPComponent p (Istar p M D) (Istar p M D) := istar_component_self_of_a h139a
  set I := Istar p M D with hIdef
  set K := L1of p M D L0 with hK
  have hKI : K ≤ I := L1_le_istar h
  have hKn : (K.subgroupOf I).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKI).2 fun g hg => by
      rw [mem_normalizer_iff_gLBConj_eq]
      exact Lemma1313.L1of_gLBConj_eq_of_mem_istar hg
  have hKperf : ⁅K, K⁆ = K := bConjJoin_perfect (B := I) (J := L0) (glaPComponent_perfect h.hL0)
  have hQ : CFSG.Open.IsQuasisimple (↥I ⧸ GLAPPrimeCore p ↥I) :=
    Lemma1313.isQuasisimple_barOf_of_pComp hI
  have hnormal : (barX p I K).Normal := Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  rcases Lemma1313.normal_central_or_top hnormal hQ with hc | htop
  · exfalso
    have hperf : ⁅barX p I K, barX p I K⁆ = barX p I K := barX_perfect p hKI hKperf
    have hcomm : ⁅barX p I K, barX p I K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hc.trans (Subgroup.center_le_centralizer _))
    have hbot : barX p I K = ⊥ := by rw [← hperf, hcomm]
    have hL0K : L0 ≤ K := Lemma1313.le_L1of'
    have hbot' : barX p I (⊥ : Subgroup G) = ⊥ := by
      unfold barX
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    have hle : barX p I L0 ≤ barX p I (⊥ : Subgroup G) := by
      rw [hbot']
      exact (bmono p hL0K).trans (le_of_eq hbot)
    have hIM : IsSubnormal I M := istar_isSubnormal p M D
    have hL0IM : L0 ≤ I := L0_le_istar h
    have hL0O : L0 ≤ GLAPPrimeCoreOf p M := by
      intro x hx
      obtain ⟨j, hj, hjx⟩ := exists_of_barX_le hle hx (hL0IM hx)
      have hj1 : j = 1 := Subgroup.mem_bot.1 hj
      rw [hj1, inv_one, one_mul] at hjx
      exact glaPPrimeCoreOf_le_of_isSubnormal hp hIM hjx
    apply h.notCov
    have hM0 : barX p M L0 ≤ barX p M (⊥ : Subgroup G) :=
      barX_le_of_forall (bot_le : (⊥ : Subgroup G) ≤ M) (fun k hk => ⟨1, Subgroup.one_mem _, by
        rw [inv_one, one_mul]; exact hL0O hk⟩)
    have hbotM : barX p M (⊥ : Subgroup G) = ⊥ := by
      unfold barX
      rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
    rw [hbotM] at hM0
    exact hM0.trans bot_le
  · by_contra hne
    exact hI.2.2.2 K (lt_of_le_of_ne hKI hne) (IsSubnormal.step hKI hKn (IsSubnormal.refl I))
      (htop.trans (barX_self p I).symm)

theorem tbar_not_centralize_Iof (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) :
    ¬ barX p M T ≤ Subgroup.centralizer
      ((barX p M (Iof p M D) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hB : IsBOneMax p B := h.bOne
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS hB h.pre
  obtain ⟨hpc, hcent, hcomp⟩ := hP95 G m p hS M D
    (prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD)
  have hPM : gammaStar p D ≤ M :=
    (prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h.toSec11 h.hD).2
  have hTM : T ≤ M := h.hT2.trans hPM
  have hTΓ : barX p M T ≤ barX p M (gammaStar p D) := bmono p h.hT2
  have hTD : barX p M T ≤ barX p M (gammaD D) :=
    bmono p (h.hT2.trans (gammaStar_le_gammaD p D))
  intro hTI
  have hcc : ∀ L : Subgroup G, GLAPComponent p M L →
      barX p M T ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    intro L hL
    by_cases hc : barX p M (gammaStar p D) ≤ Subgroup.centralizer
        ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))
    · exact hTΓ.trans hc
    · have hle : L ≤ Iof p M D := le_iSup_of_le L (le_iSup_of_le ⟨hL, hc⟩ le_rfl)
      exact hTI.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (bmono p hle)))
  have hQcore : GLAPPrimeCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hxfix : barX p M T ≤ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) := by
    intro x hx
    apply mem_pCore_of_centralizes hp hQcore
    · exact hcent (hTD hx)
    · intro K hK
      obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq M hK
      exact hcc L hL hx
  have hT2 : IsPGroup 2 ↥T := (isPGroup_gammaStar p D).to_le h.hT2
  have hT2' : IsPGroup 2 ↥(barX p M T) := by
    have hsub : IsPGroup 2 ↥(T.subgroupOf M) :=
      hT2.comap_of_injective M.subtype Subtype.val_injective
    exact hsub.map _
  have hbarT : barX p M T = ⊥ := by
    have hpC : IsPGroup p ↥(CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)) :=
      CFSG.LieType.BorelTits.pCore_isPGroup p
    have hI : barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) = ⊥ := by
      have h2 : IsPGroup 2 ↥(barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)) :=
        hT2'.to_le inf_le_left
      have hpp : IsPGroup p ↥(barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M)) :=
        hpC.to_le inf_le_right
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 h2
      obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hpp
      have hb0 : b = 0 := by
        by_contra hb0
        have hdvd : p ∣ 2 ^ a := by
          rw [← ha, hb]
          exact dvd_pow_self p hb0
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
      exact Subgroup.eq_bot_of_card_eq _ (by rw [hb, hb0, pow_zero])
    calc barX p M T = barX p M T ⊓ CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) :=
          (inf_eq_left.2 hxfix).symm
      _ = ⊥ := hI
  have hTp' : T ≤ GLAPPrimeCoreOf p M := by
    intro t ht
    have h1 : (QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨t, hTM ht⟩ : ↥M)) ∈ barX p M T :=
      ⟨⟨t, hTM ht⟩, (Subgroup.mem_subgroupOf).2 ht, rfl⟩
    rw [hbarT, Subgroup.mem_bot] at h1
    have h2 := (QuotientGroup.eq_one_iff (⟨t, hTM ht⟩ : ↥M)).1 h1
    unfold GLAPPrimeCoreOf
    exact Subgroup.mem_map.2 ⟨⟨t, hTM ht⟩, h2, rfl⟩
  have hTΓD : T ≤ gammaD D ⊓ GLAPPrimeCoreOf p M :=
    le_inf (h.hT2.trans (gammaStar_le_gammaD p D)) hTp'
  rw [hpc] at hTΓD
  have hTeq : T = pCoreOf 2 M := le_antisymm hTΓD h.hT1
  have hM2ne : pCoreOf 2 M ≠ ⊥ := by
    intro h0
    have hcharM := hS.charTwo M h.pre.1.1
    rw [h0] at hcharM
    have hMb : M ≤ ⊥ := by
      intro x hx
      have hxc : x ∈ Subgroup.centralizer (((⊥ : Subgroup G)) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hg
        rw [hg, one_mul, mul_one]
      exact hcharM ⟨hx, hxc⟩
    have hBb : B = ⊥ := le_bot_iff.1 (hBM.trans hMb)
    obtain ⟨x, y, hxy⟩ := (hS.nontrivial hB).exists_pair_ne
    apply hxy
    apply Subtype.ext
    have hx : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hBb]
      exact x.2
    have hy : (y : G) ∈ (⊥ : Subgroup G) := by
      rw [← hBb]
      exact y.2
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  have hIT : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 M : Set G)) :=
    ⟨pCoreOf 2 M, hM2ne, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, rfl⟩
  have hmax : Subgroup.normalizer (pCoreOf 2 M : Set G) = M :=
    h.pre.1.2 _ hIT (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  apply h.hN
  rw [hTeq, hmax]

theorem t1_of_caseA (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) (hL137i : Lemma137_iStatement)
    {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) :
    Nat.Coprime p (Nat.card T) ∧ T ≤ Subgroup.normalizer (L1of p M D L0 : Set G) ∧
      B ≤ Subgroup.normalizer (T : Set G) ∧
      L1of p M D L0 ≤ ⁅L1of p M D L0, T⁆ ⊔ GLAPPrimeCoreOf p (L1of p M D L0) := by
  have hp : p.Prime := GLStanding.prime h.standing
  have hp2 : p ≠ 2 := GLStanding.ne_two h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  have hT2 : IsPGroup 2 ↥T := (isPGroup_gammaStar p D).to_le h.hT2
  have hPM : gammaStar p D ≤ M :=
    (prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h.toSec11 h.hD).2
  have hTM : T ≤ M := h.hT2.trans hPM
  have hKeq : L1of p M D L0 = Istar p M D := L1_eq_istar_of_a h h139a
  have hTN : T ≤ Subgroup.normalizer (Istar p M D : Set G) := fun t ht => by
    rw [mem_normalizer_iff_gLBConj_eq]
    exact istar_conj_eq p (hTM ht)
  refine ⟨coprime_card_of_isPGroup_two hp hp2 hT2, by rw [hKeq]; exact hTN, hL137i h.toSec13, ?_⟩
  rw [hKeq]
  have hnc := tbar_not_centralize_Iof h111 h1117 h121 h127 hP95 h.toSec13
  rw [h139a.2.1] at hnc
  exact le_commutator_sup_core hp (istar_isSubnormal p M D) (istar_component_self_of_a h139a) hTN hnc

theorem lemma1313_i_caseA (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) (hL137i : Lemma137_iStatement)
    {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) {U : Subgroup G}
    (hU : IsU1312 p B M D L0 d U) {b : G} (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1) :
    ∃ S : Set (Subgroup G), (∀ X ∈ S, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) X) ∧
      GLAPLayer p (L1of p M D L0 ⊓ Subgroup.centralizer ({b} : Set G)) = ⨆ X ∈ S, X := by
  obtain ⟨hcop, hTK, hBT, hgen⟩ := t1_of_caseA h111 h1117 h121 h127 hP95 hL137i h h139a
  exact lemma1313_i_of_T1 hSch i11 h hU hb hb1 hcop hTK hBT hgen

end CaseA

section SylowTwo

variable {G : Type} [Group G] [Finite G]

theorem eq_commutator_of_sylow_two {K : Subgroup G} (hK : ⁅K, K⁆ = K) (P : Sylow 2 ↥K) :
    ⁅K, (P : Subgroup ↥K).map K.subtype⁆ = K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T : Subgroup G := (P : Subgroup ↥K).map K.subtype with hT
  have hTK : T ≤ K := Subgroup.map_subtype_le _
  set N : Subgroup G := ⁅K, T⁆ with hN
  have hNK : N ≤ K := commutator_le_of_le' le_rfl hTK
  haveI hNn : (N.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (Subgroup.normalizer_commutator_ge_left K T)
  let ρ : ↥K →* (↥K ⧸ N.subgroupOf K) := QuotientGroup.mk' (N.subgroupOf K)
  have hρ : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  let P' : Sylow 2 (↥K ⧸ N.subgroupOf K) := P.mapSurjective hρ
  have hP'eq : (P' : Subgroup (↥K ⧸ N.subgroupOf K)) = (P : Subgroup ↥K).map ρ :=
    Sylow.coe_mapSurjective hρ P
  have hcent : ∀ x ∈ (P' : Subgroup (↥K ⧸ N.subgroupOf K)), ∀ y, y * x = x * y := by
    intro x hx y
    rw [hP'eq] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := hρ y
    have h1 : ⁅k, t⁆ ∈ N.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      have : ((⁅k, t⁆ : ↥K) : G) = ⁅(k : G), (t : G)⁆ := by simp [commutatorElement_def]
      rw [this]
      exact Subgroup.commutator_mem_commutator k.2 ⟨t, ht, rfl⟩
    have h2 : ρ ⁅k, t⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h1
    rw [map_commutatorElement] at h2
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  have hP'cent : Subgroup.normalizer (P' : Set (↥K ⧸ N.subgroupOf K)) ≤
      Subgroup.centralizer (P' : Set (↥K ⧸ N.subgroupOf K)) := fun g _ =>
    Subgroup.mem_centralizer_iff.2 fun h hh => (hcent h hh g).symm
  have hPcomm : ∀ a b : ↥P', a * b = b * a := fun a b => Subtype.ext (hcent (a : _) a.2 b).symm
  haveI : IsMulCommutative ↥P' := ⟨⟨hPcomm⟩⟩
  have hKtop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = (⊤ : Subgroup ↥K) := by
    have h1 : (⁅K, K⁆).subgroupOf K = ⁅K.subgroupOf K, K.subgroupOf K⁆ :=
      subgroupOf_commutator le_rfl le_rfl
    rw [hK, Subgroup.subgroupOf_self] at h1
    exact h1.symm
  have hQtop : ⁅(⊤ : Subgroup (↥K ⧸ N.subgroupOf K)), (⊤ : Subgroup (↥K ⧸ N.subgroupOf K))⁆ =
      (⊤ : Subgroup (↥K ⧸ N.subgroupOf K)) := by
    have := Subgroup.map_commutator (⊤ : Subgroup ↥K) (⊤ : Subgroup ↥K) ρ
    rw [hKtop, Subgroup.map_top_of_surjective ρ hρ] at this
    exact this.symm
  let f := MonoidHom.transferSylow P' hP'cent
  have hf : ∀ q, f q = 1 := by
    intro q
    have hker : (⊤ : Subgroup (↥K ⧸ N.subgroupOf K)) ≤ f.ker := by
      rw [← hQtop]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hPcomm _ _)
    exact MonoidHom.mem_ker.1 (hker (Subgroup.mem_top q))
  have hP'bot : (P' : Subgroup (↥K ⧸ N.subgroupOf K)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 := MonoidHom.transferSylow_eq_pow P' hP'cent x hx
    rw [hf x] at h1
    have h2 : (x ^ (P' : Subgroup (↥K ⧸ N.subgroupOf K)).index) = 1 := by
      have := congrArg Subtype.val h1
      simpa using this.symm
    have hinj := (P'.2.powEquiv' P'.not_dvd_index).injective
    have : (⟨x, hx⟩ : ↥P') = 1 := by
      apply hinj
      show (⟨x, hx⟩ : ↥P') ^ (P' : Subgroup (↥K ⧸ N.subgroupOf K)).index = 1 ^ _
      apply Subtype.ext
      simpa using h2
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hodd : Odd (Nat.card (↥K ⧸ N.subgroupOf K)) := by
    have h1 := P'.not_dvd_index
    rw [hP'bot, Subgroup.index_bot] at h1
    exact Nat.odd_iff.2 (by omega)
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  haveI : Group.IsPerfect (↥K ⧸ N.subgroupOf K) := ⟨by simpa [commutator_def] using hQtop⟩
  have hsub : Subsingleton (↥K ⧸ N.subgroupOf K) := by
    by_contra hns
    haveI : Nontrivial (↥K ⧸ N.subgroupOf K) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isSolvable _ hsolv
  refine le_antisymm hNK fun k hk => ?_
  have h1 : ρ ⟨k, hk⟩ = 1 := Subsingleton.elim _ _
  exact (Subgroup.mem_subgroupOf).1 ((QuotientGroup.eq_one_iff _).1 h1)

end SylowTwo

section CaseB

variable {G : Type} [Group G] [Finite G]

@[expose] def T1CaseB : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D →
      ∃ P : Sylow 2 ↥(L1of p M D L0),
        B ≤ Subgroup.normalizer (((P : Subgroup ↥(L1of p M D L0)).map (L1of p M D L0).subtype :
          Subgroup G) : Set G)

theorem t1_of_caseB {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (P : Sylow 2 ↥(L1of p M D L0)) :
    IsPGroup 2 ↥((P : Subgroup ↥(L1of p M D L0)).map (L1of p M D L0).subtype) ∧
      (P : Subgroup ↥(L1of p M D L0)).map (L1of p M D L0).subtype ≤ L1of p M D L0 ∧
      L1of p M D L0 ≤ ⁅L1of p M D L0, (P : Subgroup ↥(L1of p M D L0)).map (L1of p M D L0).subtype⁆ ⊔
        GLAPPrimeCoreOf p (L1of p M D L0) := by
  have hKperf : ⁅L1of p M D L0, L1of p M D L0⁆ = L1of p M D L0 :=
    bConjJoin_perfect (B := Istar p M D) (J := L0) (glaPComponent_perfect h.hL0)
  refine ⟨P.2.of_equiv ((P : Subgroup ↥(L1of p M D L0)).equivMapOfInjective
      (L1of p M D L0).subtype (L1of p M D L0).subtype_injective), Subgroup.map_subtype_le _, ?_⟩
  rw [eq_commutator_of_sylow_two hKperf P]
  exact le_sup_left

end CaseB

section HBal

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}

theorem gLBConj_eq_of_le_centralizer {L0 : Subgroup G} {x : G}
    (hL : L0 ≤ Subgroup.centralizer ({x} : Set G)) : GLBConj x L0 = L0 ∧ GLBConj x⁻¹ L0 = L0 := by
  have key : ∀ y ∈ L0, x * y * x⁻¹ = y := fun y hy => by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hL hy)
    rw [← this]
    group
  have key' : ∀ y ∈ L0, x⁻¹ * y * x = y := fun y hy => by
    have := Subgroup.mem_centralizer_singleton_iff.1 (hL hy)
    rw [mul_assoc, this]
    group
  constructor
  · ext y
    rw [mem_gLBConj]
    constructor
    · intro h
      have := key _ h
      have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [← e, key' _ h]
      exact h
    · intro h
      rw [key _ h]
      exact h
  · ext y
    rw [mem_gLBConj]
    constructor
    · intro h
      have e : x * (x⁻¹ * y * x⁻¹⁻¹) * x⁻¹ = y := by group
      rw [← e, key _ h]
      exact h
    · intro h
      simpa [key' _ h] using h

theorem gLBConj_L1of_eq {p : ℕ} {M D L0 : Subgroup G} {d : G} (hdM : d ∈ M)
    (hL : L0 ≤ Subgroup.centralizer ({d} : Set G)) :
    GLBConj d (L1of p M D L0) = L1of p M D L0 := by
  have hle : ∀ x ∈ M, GLBConj x L0 = L0 → GLBConj x (L1of p M D L0) ≤ L1of p M D L0 := by
    intro x hxM hxL
    unfold L1of
    rw [gLBConj_iSup_eq]
    refine iSup_le fun g => ?_
    by_cases hg : g ∈ Istar p M D
    · rw [iSup_pos hg, Lemma1313.gLBConj_gLBConj_mul']
      have hg' : x⁻¹ * g * x ∈ Istar p M D := by
        have : x⁻¹ * g * x ∈ GLBConj x (Istar p M D) := by
          rw [mem_gLBConj]
          have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
          rw [e]
          exact hg
        rwa [istar_conj_eq p hxM] at this
      have e : GLBConj (g * x) L0 = GLBConj (x⁻¹ * g * x) L0 := by
        rw [show g * x = x * (x⁻¹ * g * x) by group,
          ← Lemma1313.gLBConj_gLBConj_mul' (x⁻¹ * g * x) x L0, hxL]
      rw [e]
      exact le_iSup₂_of_le (x⁻¹ * g * x) hg' le_rfl
    · rw [iSup_neg hg]
      unfold GLBConj
      rw [Subgroup.map_bot]
      exact bot_le
  obtain ⟨h1, h2⟩ := gLBConj_eq_of_le_centralizer hL
  refine le_antisymm (hle d hdM h1) ?_
  have := gLBConj_mono d (hle d⁻¹ (M.inv_mem hdM) h2)
  rwa [gLBConj_gLBConj_inv] at this

theorem hBal_of_clause_i (i2 : CFSG.HardMathSupport.Solomon.LocalBalance.Input18_2One)
    (h : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (hU : IsU1312 p B M D L0 d U) {b : G}
    (hb : b ∈ centBar p U (L1of p M D L0)) (hb1 : b ≠ 1)
    (hi : ∃ S : Set (Subgroup G),
      (∀ X ∈ S, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) X) ∧
        GLAPLayer p (L1of p M D L0 ⊓ Subgroup.centralizer ({b} : Set G)) = ⨆ X ∈ S, X) :
    GLAPComponent p (Subgroup.centralizer ({b, d} : Set G))
      (GLAPLayer p (L0 ⊓ Subgroup.centralizer ({b} : Set G))) := by
  have hp : p.Prime := GLStanding.prime h.standing
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hbord, hbM, hbC, hnorm, hcomm, hL0M, hquasi⟩ := Lemma1313.setting_facts h hU hb hb1
  set K := L1of p M D L0 with hK
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set Cd := Subgroup.centralizer ({d} : Set G) with hCd
  have hdD : d ∈ D := h.hd.1
  have hdb : d * b = b * d := Subgroup.mem_centralizer_iff.1 hbC d (Set.mem_singleton d)
  have hY₀c : GLAPComponent p (L0 ⊓ Cb) (GLAPLayer p (L0 ⊓ Cb)) :=
    (glaPComponent_layer_inf_cent hbord hnorm hcomm hquasi).1
  obtain ⟨S, hS, -, hEq⟩ := Lemma1311.pComp_piLayer_summand hp h.hL0
  have hL0N : GLAPComponent p (Istar p M D ⊓ Cd) L0 := by rw [hEq]; exact hS
  have hL0d : L0 ≤ Cd := hL0N.1.trans inf_le_right
  have hL0K : GLAPComponent p (K ⊓ Cd) L0 :=
    glaPComponent_of_le hp hL0N (le_inf Lemma1313.le_L1of' hL0d)
      (inf_le_inf_right Cd (L1_le_istar h))
  have hsn1 : IsSubnormal (L0 ⊓ Cb) ((K ⊓ Cd) ⊓ Cb) := isSubnormal_inf hL0K.2.1 Cb
  have hY₀Z : GLAPComponent p ((K ⊓ Cd) ⊓ Cb) (GLAPLayer p (L0 ⊓ Cb)) :=
    glaPComponent_up hp hY₀c hsn1
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hdM : d ∈ M := hAM (h.hD.1 hdD)
  have hdN : d ∈ Subgroup.normalizer ((K ⊓ Cb : Subgroup G) : Set G) :=
    mem_normalizer_inf (mem_normalizer_iff_gLBConj_eq.2 (gLBConj_L1of_eq hdM hL0d))
      (mem_normalizer_iff_gLBConj_eq.2
        (Lemma1313.gLBConj_centralizer_singleton_of_comm hdb.symm))
  have hdCb : d ∈ Cb := Subgroup.mem_centralizer_singleton_iff.2 hdb
  have htop : (K ⊓ Cb) ⊔ Subgroup.zpowers d ≠ ⊤ := by
    intro htop
    have hle : (K ⊓ Cb) ⊔ Subgroup.zpowers d ≤ Cb :=
      sup_le inf_le_right ((Subgroup.zpowers_le).2 hdCb)
    exact centralizer_singleton_ne_top h.standing hb1 (top_le_iff.1 (htop ▸ hle))
  have hdE : IsElemAbelian p (Subgroup.zpowers d) :=
    isElemAbelian_mono h.hD.2.1 ((Subgroup.zpowers_le).2 hdD)
  have hbal := layer_inf_cent_le_of_balance i2 hp h.standing.kProper hdE hdN htop
  have hY₀L : GLAPLayer p (L0 ⊓ Cb) ≤ GLAPLayer p (K ⊓ Cb) := by
    have h1 : GLAPLayer p (L0 ⊓ Cb) ≤ GLAPLayer p ((K ⊓ Cd) ⊓ Cb) := le_sSup hY₀Z
    rw [inf_right_comm] at h1
    exact h1.trans hbal
  obtain ⟨𝒮, h𝒮c, h𝒮eq⟩ := hi
  have hL1bsn : IsSubnormal (GLAPLayer p (K ⊓ Cb)) Cb := by
    rw [h𝒮eq, ← sSup_eq_iSup]
    exact isSubnormal_sSup_of_forall' 𝒮 fun X hX => ⟨(h𝒮c X hX).1, (h𝒮c X hX).2.1⟩
  have hlayer_le : GLAPLayer p (K ⊓ Cb) ≤ K ⊓ Cb := sSup_le fun L hL => hL.1
  set V := GLAPLayer p (K ⊓ Cb) ⊓ Cd with hV
  have hY₀Cd : GLAPLayer p (L0 ⊓ Cb) ≤ Cd := hY₀Z.1.trans (inf_le_left.trans inf_le_right)
  have hVZ : V ≤ (K ⊓ Cd) ⊓ Cb := by
    intro x hx
    have h1 := hlayer_le hx.1
    exact ⟨⟨h1.1, hx.2⟩, h1.2⟩
  have hY₀V : GLAPComponent p V (GLAPLayer p (L0 ⊓ Cb)) :=
    glaPComponent_of_le hp hY₀Z (le_inf hY₀L hY₀Cd) hVZ
  have hVsn : IsSubnormal V (Cb ⊓ Cd) := isSubnormal_inf hL1bsn Cd
  have hfin := glaPComponent_up hp hY₀V hVsn
  rw [centralizer_pair_eq]
  exact hfin

end HBal

section InputL0

@[expose] def InputL0CoreB : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G},
    Cex1310 G m p B M E A D T R L0 d → Prop139b p M D → GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M

end InputL0

section NotPCentral

variable {G : Type} [Group G] [Finite G]

theorem card_barOf_mul_core (p : ℕ) (L : Subgroup G) :
    Nat.card (barOf p L) * Nat.card (GLAPPrimeCoreOf p L) = Nat.card L := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore p ↥L)
  have h2 : Nat.card ↥(GLAPPrimeCoreOf p L) = Nat.card ↥(GLAPPrimeCore p ↥L) := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.card_map_of_injective (f := L.subtype) Subtype.val_injective
  rw [h2]
  exact h1.symm

theorem card_barX_eq_card_barOf {p : ℕ} (hp : p.Prime) {M L : Subgroup G} (hLM : L ≤ M)
    (hcore : GLAPPrimeCoreOf p M ⊓ L = GLAPPrimeCoreOf p L) :
    Nat.card (barX p M L) = Nat.card (barOf p L) := by
  have h1 := card_eq_card_inter_mul_card_barX hp hLM
  rw [hcore] at h1
  have h2 := card_barOf_mul_core p L
  have hpos : 0 < Nat.card (GLAPPrimeCoreOf p L) := Nat.card_pos
  have : Nat.card (barX p M L) * Nat.card (GLAPPrimeCoreOf p L) =
      Nat.card (barOf p L) * Nat.card (GLAPPrimeCoreOf p L) := by
    rw [mul_comm (Nat.card (barX p M L)), ← h1, h2]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem barX_eq_of_iso {p : ℕ} (hp : p.Prime) {M I L : Subgroup G} (hIM : IsSubnormal I M)
    (hLI : L ≤ I) (hcoreL : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p M)
    (e : Nonempty (barOf p L ≃* barOf p I)) : barX p M L = barX p M I := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ M := hLI.trans hIM.le
  have hcL : GLAPPrimeCoreOf p M ⊓ L = GLAPPrimeCoreOf p L := by
    refine le_antisymm (fun z hz => ?_) (le_inf hcoreL (Lemma1313.glaPPrimeCoreOf_le_self L))
    exact Lemma1313.mem_glaPPrimeCoreOf_of_mem_of_normalized (I := M) (P := L)
      (N := GLAPPrimeCoreOf p M) hLM
      (fun q hq => gLBConj_eq_of_mem_normalizer (le_normalizer_glaPPrimeCoreOf p M hq))
      (Lemma1313.coprime_card_glaPPrimeCoreOf p M) hz.1 hz.2
  have hcI : GLAPPrimeCoreOf p M ⊓ I = GLAPPrimeCoreOf p I := by
    rw [inf_comm]
    exact glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hIM
  obtain ⟨e⟩ := e
  have hcard : Nat.card (barX p M I) ≤ Nat.card (barX p M L) := by
    rw [card_barX_eq_card_barOf hp hLM hcL, card_barX_eq_card_barOf hp hIM.le hcI]
    exact (Nat.card_congr e.toEquiv).ge
  exact Subgroup.eq_of_le_of_card_ge (bmono p hLI) hcard

theorem core_le_of_iso {p : ℕ} (hp : p.Prime) {I L : Subgroup G} (hLI : L ≤ I)
    (e : Nonempty (barOf p L ≃* barOf p I)) : GLAPPrimeCoreOf p L ≤ GLAPPrimeCoreOf p I := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := e
  have hC0 : GLAPPrimeCoreOf p I ⊓ L ≤ GLAPPrimeCoreOf p L := fun z hz =>
    Lemma1313.mem_glaPPrimeCoreOf_of_mem_of_normalized (I := I) (P := L) (N := GLAPPrimeCoreOf p I) hLI
      (fun q hq => gLBConj_eq_of_mem_normalizer (le_normalizer_glaPPrimeCoreOf p I hq))
      (Lemma1313.coprime_card_glaPPrimeCoreOf p I) hz.1 hz.2
  have h1 := card_eq_card_inter_mul_card_barX hp hLI
  have h2 := card_barOf_mul_core p L
  have h3 : Nat.card (barX p I L) ≤ Nat.card (barOf p I) := by
    have : Nat.card (barX p I L) ≤ Nat.card (⊤ : Subgroup (↥I ⧸ GLAPPrimeCore p ↥I)) :=
      Subgroup.card_le_of_le le_top
    rwa [Subgroup.card_top] at this
  have h4 : Nat.card (barOf p L) = Nat.card (barOf p I) := Nat.card_congr e.toEquiv
  have hpos : 0 < Nat.card (barOf p I) := Nat.card_pos
  have h5 : Nat.card (GLAPPrimeCoreOf p L) ≤ Nat.card (GLAPPrimeCoreOf p I ⊓ L : Subgroup G) := by
    have h6 : Nat.card (barOf p I) * Nat.card (GLAPPrimeCoreOf p L) ≤
        Nat.card (barOf p I) * Nat.card (GLAPPrimeCoreOf p I ⊓ L : Subgroup G) := by
      calc Nat.card (barOf p I) * Nat.card (GLAPPrimeCoreOf p L)
          = Nat.card L := by rw [← h4]; exact h2
        _ = Nat.card (GLAPPrimeCoreOf p I ⊓ L : Subgroup G) * Nat.card (barX p I L) := h1
        _ ≤ Nat.card (GLAPPrimeCoreOf p I ⊓ L : Subgroup G) * Nat.card (barOf p I) :=
            Nat.mul_le_mul_left _ h3
        _ = Nat.card (barOf p I) * Nat.card (GLAPPrimeCoreOf p I ⊓ L : Subgroup G) := mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h6 hpos
  have heq : GLAPPrimeCoreOf p I ⊓ L = GLAPPrimeCoreOf p L :=
    Subgroup.eq_of_le_of_card_ge hC0 h5
  rw [← heq]
  exact inf_le_left

theorem l0core_of_a {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) :
    GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M := by
  have hp : p.Prime := GLStanding.prime h.standing
  obtain ⟨e⟩ := h.hL0iso (Istar p M D) (istar_component_self_of_a h139a)
  exact (core_le_of_iso hp (L0_le_istar h) ⟨e⟩).trans
    (glaPPrimeCoreOf_le_of_isSubnormal hp (istar_isSubnormal p M D))

theorem l0core_of_inputs (hB : InputL0CoreB) {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) : GLAPPrimeCoreOf p L0 ≤ GLAPPrimeCoreOf p M := by
  rcases h.h139 with h139a | h139b
  · exact l0core_of_a h h139a
  · exact hB h h139b

end NotPCentral

section NotPCentralMain

variable {G : Type} [Group G] [Finite G]

theorem notPCentral_of_inputs (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) (hL137i : Lemma137_iStatement)
    {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D) : ¬ IsPCentralIn p M d := by
  rintro ⟨P, hP, hdZ⟩
  have hSt := h.standing
  have hp : p.Prime := GLStanding.prime hSt
  have hp2 : p ≠ 2 := GLStanding.ne_two hSt
  haveI : Fact p.Prime := ⟨hp⟩
  have hB : IsBOneMax p B := h.bOne
  set I := Istar p M D with hIdef
  have hIc : GLAPComponent p I I := istar_component_self_of_a h139a
  have hIM : IsSubnormal I M := istar_isSubnormal p M D
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hdD : d ∈ D := h.hd.1
  have hdM : d ∈ M := hAM (h.hD.1 hdD)
  have hdord : orderOf d = p := orderOf_eq_prime (h.hD.2.1.2 d hdD) h.hd.2
  have hL0I : L0 ≤ I := L0_le_istar h
  have hL0M : L0 ≤ M := hL0I.trans hIM.le
  have hL0d : L0 ≤ Subgroup.centralizer ({d} : Set G) :=
    (h.hL0.1.trans (Lemma1313.piLayer_le_self' p _)).trans inf_le_right
  have hINorm : ∀ g ∈ M, g ∈ Subgroup.normalizer (I : Set G) := fun g hg => by
    rw [mem_normalizer_iff_gLBConj_eq]
    exact istar_conj_eq p hg
  have hOMn : ∀ g ∈ M, g ∈ Subgroup.normalizer ((GLAPPrimeCoreOf p M : Subgroup G) : Set G) :=
    fun g hg => le_normalizer_glaPPrimeCoreOf p M hg
  have hbarEq : barX p M L0 = barX p M I := by
    obtain ⟨e⟩ := h.hL0iso I hIc
    exact barX_eq_of_iso hp hIM hL0I (l0core_of_a h h139a) ⟨e⟩
  have hdI : d ∈ actTriv p I := by
    refine ⟨hINorm d hdM, fun y hy => ?_⟩
    have hle : barX p M I ≤ barX p M L0 := le_of_eq hbarEq.symm
    obtain ⟨j, hj, hjy⟩ := exists_of_barX_le hle hy (hIM.le hy)
    have hjd : d * j = j * d := (Subgroup.mem_centralizer_singleton_iff.1 (hL0d hj)).symm
    have hjM : j ∈ M := hL0M hj
    have e : d * y * d⁻¹ * y⁻¹ = j * (d * (j⁻¹ * y) * d⁻¹ * (j⁻¹ * y)⁻¹) * j⁻¹ := by
      have e1 : d * y * d⁻¹ * y⁻¹ = (d * j) * (j⁻¹ * y) * d⁻¹ * (j⁻¹ * y)⁻¹ * j⁻¹ := by group
      rw [e1, hjd]
      group
    have hz : d * (j⁻¹ * y) * d⁻¹ * (j⁻¹ * y)⁻¹ ∈ GLAPPrimeCoreOf p M :=
      (GLAPPrimeCoreOf p M).mul_mem ((Subgroup.mem_normalizer_iff.1 (hOMn d hdM) _).1 hjy)
        ((GLAPPrimeCoreOf p M).inv_mem hjy)
    have hzM : d * y * d⁻¹ * y⁻¹ ∈ GLAPPrimeCoreOf p M := by
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hOMn j hjM) _).1 hz
    have hzI : d * y * d⁻¹ * y⁻¹ ∈ I :=
      I.mul_mem ((Subgroup.mem_normalizer_iff.1 (hINorm d hdM) y).1 hy) (I.inv_mem hy)
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hIM]
    exact ⟨hzI, hzM⟩
  obtain ⟨x, hxM, hxP⟩ := Lemma1314b.exists_gLBConj_eq h.hR.1 hP
  set b' : G := x * d * x⁻¹ with hb'def
  have hb'M : b' ∈ M := M.mul_mem (M.mul_mem hxM hdM) (M.inv_mem hxM)
  have hb'ZR : b' ∈ centerOf R := by
    have h1 : b' ∈ GLBConj x⁻¹ (centerOf P) := by
      rw [mem_gLBConj]
      have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
      rw [hb'def, e]
      exact hdZ
    have h2 := Lemma1314b.gLBConj_centerOf_le x⁻¹ P h1
    rw [← hxP, gLBConj_inv_gLBConj] at h2
    exact h2
  have hBR : B ≤ R := le_sup_right.trans h.hR.2
  have hb'comm : ∀ g ∈ B, b' * g = g * b' := fun g hg =>
    (((Lemma1314b.mem_centerOf_iff_aux R b').1 hb'ZR).2 g (hBR hg)).symm
  have hb'p : b' ^ p = 1 := by
    rw [hb'def, conj_pow, h.hD.2.1.2 d hdD]
    group
  have hb'1 : b' ≠ 1 := by
    intro h1
    apply h.hd.2
    have : d = x⁻¹ * b' * x := by rw [hb'def]; group
    rw [this, h1]
    group
  have hDe : IsElemAbelian p (GLBConj x⁻¹ D) := CFSG.SectionRank.isElemAbelian_map h.hD.2.1 _
  have hb'D : b' ∈ GLBConj x⁻¹ D := by
    rw [mem_gLBConj]
    have e : x⁻¹ * (x * d * x⁻¹) * x⁻¹⁻¹ = d := by group
    rw [hb'def, e]
    exact hdD
  have hzel : IsElemAbelian p (Subgroup.zpowers b') :=
    isElemAbelian_mono hDe ((Subgroup.zpowers_le).2 hb'D)
  have hSC : IsSCp p ⊤ B := lemma23_proved G m p hSt B hB
  have hb'B : b' ∈ B := by
    have hEl : IsElemAbelian p (B ⊔ Subgroup.zpowers b') :=
      isElemAbelian_sup_of_commute hB.1.1 hzel fun g hg =>
        Lemma1314b.mem_centralizer_zpowers_aux (hb'comm g hg)
    have := hSC.2.2 (B ⊔ Subgroup.zpowers b') le_top hEl le_sup_left
    rw [← this]
    exact (le_sup_right : Subgroup.zpowers b' ≤ B ⊔ Subgroup.zpowers b') (Subgroup.mem_zpowers b')
  have hb'I : b' ∈ actTriv p I := conj_mem_actTriv (hINorm x hxM) hdI
  have hKeq : L1of p M D L0 = Istar p M D := L1_eq_istar_of_a h h139a
  obtain ⟨hcop, hTK, hBT, hgen⟩ := t1_of_caseA h111 h1117 h121 h127 hP95 hL137i h h139a
  rw [hKeq] at hTK hgen
  obtain ⟨𝒮, h𝒮c, h𝒮eq⟩ := layer_components hSch i11 hSt hB h.pre hb'B hb'1 hIM hb'I hcop hTK hBT hgen
  have hbord' : orderOf b' = p := orderOf_eq_prime hb'p hb'1
  have hnormI : GLBConj b' I = I := mem_normalizer_iff_gLBConj_eq.1 (hINorm b' hb'M)
  have hquasiI : CFSG.Open.IsQuasisimple (barOf p I) :=
    Lemma1313.isQuasisimple_barOf_of_pComp hIc
  obtain ⟨hYc, hYu⟩ := glaPComponent_layer_inf_cent hbord' hnormI hb'I.2 hquasiI
  set Y := GLAPLayer p (I ⊓ Subgroup.centralizer ({b'} : Set G)) with hYdef
  have hYne : Y ≠ ⊥ := glaPComponent_ne_bot' hYc
  obtain ⟨J, hJ𝒮⟩ : 𝒮.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    apply hYne
    rw [h𝒮eq, hne]
    simp
  have hJc := h𝒮c J hJ𝒮
  have hJle : J ≤ Y := by
    rw [h𝒮eq]
    exact le_iSup₂_of_le J hJ𝒮 le_rfl
  have hYle : Y ≤ I ⊓ Subgroup.centralizer ({b'} : Set G) := sSup_le fun L hL => hL.1
  have hJ' : GLAPComponent p (I ⊓ Subgroup.centralizer ({b'} : Set G)) J :=
    glaPComponent_of_le hp hJc (hJle.trans hYle) inf_le_right
  have hJY : J = Y := hYu J hJ'
  have hYb' : GLAPComponent p (Subgroup.centralizer ({b'} : Set G)) Y := hJY ▸ hJc
  have hcentd : GLBConj x (Subgroup.centralizer ({b'} : Set G)) = Subgroup.centralizer ({d} : Set G) := by
    rw [← centralizer_singleton_gLBConj x b']
    congr 2
    rw [hb'def]
    group
  have hYd : GLAPComponent p (Subgroup.centralizer ({d} : Set G)) (GLBConj x Y) := by
    have := glaPComponent_gLBConj hYb' x
    rwa [hcentd] at this
  obtain ⟨e1⟩ := Lemma1313.barOf_glaPLayer_inf_cent_iso (L0 := I) hbord' hnormI hb'I.2 hquasiI
  obtain ⟨e2⟩ := h.hL0iso I hIc
  have hPiI : IsPiGroup p (barOf p I) := IsPiGroup.of_mulEquiv e2 (Lemma1313.isPiGroup_barOf_L0 h)
  have hPiY : IsPiGroup p (barOf p Y) := IsPiGroup.of_mulEquiv e1.symm hPiI
  have hPiYd : IsPiGroup p (barOf p (GLBConj x Y)) :=
    IsPiGroup.of_mulEquiv (conjQuotEquiv p x Y) hPiY
  have hYdPi : GLBConj x Y ≤ piOf p d := Lemma1313.le_piOf_of_comp' hYd hPiYd
  have hpiS : piOf p d ≤ piStar p D := by
    unfold piOf piStar
    exact le_iSup_of_le d (le_iSup_of_le h.hd.1 (le_iSup_of_le h.hd.2 le_sup_left))
  have hcov : barX p M I ≤ barX p M Y :=
    Lemma1313.barX_le_glaPLayer_inf_cent hIM.le
      ((glaPPrimeCoreOf_le_of_isSubnormal hp hIM)) hbord' hnormI hb'I.2 hquasiI
  have hxI : GLBConj x I = I := istar_conj_eq p hxM
  have hcovd : barX p M I ≤ barX p M (GLBConj x Y) := by
    have h2 := gLBConj_mono (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩) hcov
    rw [← barX_gLBConj_eq p hxM, ← barX_gLBConj_eq p hxM, hxI] at h2
    exact h2
  apply h.notCov
  exact (bmono p hL0I).trans (hcovd.trans (bmono p (hYdPi.trans hpiS)))

end NotPCentralMain

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1313i

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem lemma1313_i_of_inputs (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) (hL137i : Lemma137_iStatement)
    (hT1B : Lemma1313i.T1CaseB) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A : Subgroup G} {D T R L0 : Subgroup G} {d : G}
      (_ : Cex1310 G m p B M E A D T R L0 d) {U : Subgroup G} (_ : IsU1312 p B M D L0 d U) {b : G}
      (_ : b ∈ centBar p U (L1of p M D L0)) (_ : b ≠ 1),
    ∃ S : Set (Subgroup G), (∀ X ∈ S, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) X) ∧
      GLAPLayer p (L1of p M D L0 ⊓ Subgroup.centralizer ({b} : Set G)) = ⨆ X ∈ S, X := by
  intro G _ _ m p B M E A D T R L0 d h U hU b hb hb1
  rcases h.h139 with h139a | h139b
  · exact Lemma1313i.lemma1313_i_caseA hSch i11 h111 h1117 h121 h127 hP95 hL137i h h139a hU hb hb1
  · obtain ⟨P, hBP⟩ := hT1B h h139b
    obtain ⟨hT2, hTK, hgen⟩ := Lemma1313i.t1_of_caseB h P
    have hp : p.Prime := GLStanding.prime h.standing
    have hp2 : p ≠ 2 := GLStanding.ne_two h.standing
    exact Lemma1313i.lemma1313_i_of_T1 hSch i11 h hU hb hb1
      (coprime_card_of_isPGroup_two hp hp2 hT2)
      (fun t ht => Subgroup.le_normalizer (hTK ht)) hBP hgen

theorem lemma1313_of_inputsC (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (hI183 : Prop115.Input18_3Gen) (hI182 : Lemma1313.Input18_3Two)
    (hDiag : Lemma1313Z.Input18_3DiagZ)
    (i2 : CFSG.HardMathSupport.Solomon.LocalBalance.Input18_2One)
    (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) (hL137i : Lemma137_iStatement)
    (hT1B : Lemma1313i.T1CaseB) (hL0B : Lemma1313i.InputL0CoreB) : Lemma1313Statement := by
  intro G _ _ m p B M E A D T R L0 d h U hU b hb hb1
  have hi := lemma1313_i_of_inputs hSch i11 h111 h1117 h121 h127 hP95 hL137i hT1B h hU hb hb1
  have hBal := Lemma1313i.hBal_of_clause_i i2 h hU hb hb1 hi
  exact lemma1313_of_inputsZ hI183 hI182 hDiag h hU hb hb1 hBal (Lemma1313i.l0core_of_inputs hL0B h) hi

theorem notPCentralBlock_of_inputs (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (i11 : Input11_6)
    (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : CFSG.LocalAnalysis.GLTheoremB.Prop95) (hL137i : Lemma137_iStatement) :
    Lemma1314b.NotPCentralBlock :=
  fun h h139a => Lemma1313i.notPCentral_of_inputs hSch i11 h111 h1117 h121 h127 hP95 hL137i h h139a

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
