module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchIota
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2E
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2K

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_of_relIndex_two {H T : Subgroup G} (hHT : H ≤ T) (hH : H.relIndex T = 2)
    {a x : G} (ha : a ∈ T) (hx : x ∈ H) : a * x * a⁻¹ ∈ H := by
  have h := mul_mem_of_relIndex_two hH (T.mul_mem ha (hHT hx)) (T.inv_mem ha)
  have h2 := mul_mem_of_relIndex_two hH ha (hHT hx)
  rw [h, h2]
  constructor
  · intro h3
    have := H.inv_mem (h3.2 hx)
    simpa using this
  · intro h3
    rw [iff_true_right hx]
    have := H.inv_mem h3
    simpa using this

omit [Finite G] in
theorem card_map_conj' (g : G) (H : Subgroup G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H := card_map _ _

theorem relIndex_map_conj {H T : Subgroup G} (hHT : H ≤ T) {y : G}
    (hyN : y ∈ normalizer (T : Set G)) :
    H.map (MulAut.conj y).toMonoidHom ≤ T ∧
      (H.map (MulAut.conj y).toMonoidHom).relIndex T = H.relIndex T := by
  have hle : H.map (MulAut.conj y).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 hyN x).1 (hHT hx)
  refine ⟨hle, ?_⟩
  have h1 := relIndex_mul_card (H := H) (K := T)
  have h2 := relIndex_mul_card (H := H.map (MulAut.conj y).toMonoidHom) (K := T)
  rw [inf_of_le_left hHT] at h1
  rw [inf_of_le_left hle, card_map_conj'] at h2
  have hpos : 0 < Nat.card H := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)

theorem sPrime_map {S T₁ : Subgroup G} (hST : S ≤ T₁) (hS : S.relIndex T₁ = 2) {y : G}
    (hyN : y ∈ normalizer (T₁ : Set G)) (hy2 : y * y ∈ T₁) {v : G}
    (hv : v ∈ T₁ ⊔ zpowers y) (hvT : v ∉ T₁) :
    S.map (MulAut.conj v).toMonoidHom = S.map (MulAut.conj y).toMonoidHom := by
  obtain ⟨hle', hidx'⟩ := relIndex_map_conj hST hyN
  rw [hS] at hidx'
  have hva : v * y⁻¹ ∈ T₁ := ((mem_sup_zpowers_iff hyN hy2).1 hv).resolve_left hvT
  set a := v * y⁻¹
  have hv' : v = a * y := by simp [a]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have : y * x * y⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := ⟨x, hx, rfl⟩
    have := conj_mem_of_relIndex_two hle' hidx' hva this
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hv']
    have e : a * y * x * (a * y)⁻¹ = a * (y * x * y⁻¹) * a⁻¹ := by group
    rw [e]; exact this
  ·
    have h1 : (S.map (MulAut.conj v).toMonoidHom) ≤ S.map (MulAut.conj y).toMonoidHom := by
      rintro _ ⟨x, hx, rfl⟩
      have : y * x * y⁻¹ ∈ S.map (MulAut.conj y).toMonoidHom := ⟨x, hx, rfl⟩
      have := conj_mem_of_relIndex_two hle' hidx' hva this
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hv']
      have e : a * y * x * (a * y)⁻¹ = a * (y * x * y⁻¹) * a⁻¹ := by group
      rw [e]; exact this
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [card_map_conj', card_map_conj'])).ge

variable {S T₁ : Subgroup G}
  {mul : ℕ → ℕ → ℕ} (Φ : CodeIso T₁ 131072 mul) (h0 : mul 0 0 = 0) {ι vec : Array ℕ}
  (hι : IotaFacts mul ι vec) (e : S ≃* SModel) (hST : S ≤ T₁) {y : G}
  (hyN : y ∈ normalizer (T₁ : Set G))
  (hSp : ∀ g : T₁, y⁻¹ * g * y ∈ S ↔ s2InSp vec (Φ.f g) = true)

omit [Finite G] in
include h0 hι hSp in
theorem iotaF_mem (a : SModel) :
    ((iotaF Φ (ι := ι) a : T₁) : G) ∈ S.map (MulAut.conj y).toMonoidHom := by
  have h := conj_iotaF_mem Φ h0 hι hSp a
  refine ⟨_, h, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

include h0 hι hSp in
@[expose] noncomputable def iotaSHom : S →* S.map (MulAut.conj y).toMonoidHom where
  toFun a := ⟨iotaF Φ (ι := ι) (e a), iotaF_mem Φ h0 hι hSp (e a)⟩
  map_one' := by
    apply Subtype.ext
    simp only [map_one]
    exact congrArg Subtype.val ((iotaHom Φ h0 hι).map_one)
  map_mul' a b := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact congrArg Subtype.val (iotaF_mul Φ h0 hι (e a) (e b))

include h0 hι hSp in
@[expose] noncomputable def iotaS : S ≃* S.map (MulAut.conj y).toMonoidHom :=
  MulEquiv.ofBijective (iotaSHom Φ h0 hι e hSp) (by
    have hinj : Function.Injective (iotaSHom Φ h0 hι e hSp) := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact e.injective (iotaF_injective Φ h0 hι (Subtype.ext this))
    refine ⟨hinj, ?_⟩
    exact (hinj.bijective_of_nat_card_le (by rw [card_map_conj'])).2)

theorem iotaS_val (a : S) :
    ((iotaS Φ h0 hι e hSp a : S.map (MulAut.conj y).toMonoidHom) : G) =
      (iotaF Φ (ι := ι) (e a) : G) := rfl

include hST hyN in
theorem card_inf_sPrime (hS : S.relIndex T₁ = 2) (hyS : y ∉ normalizer (S : Set G)) :
    2 * Nat.card (S ⊓ S.map (MulAut.conj y).toMonoidHom : Subgroup G) = Nat.card S := by
  set S' := S.map (MulAut.conj y).toMonoidHom
  obtain ⟨hS'T, -⟩ := relIndex_map_conj hST hyN
  have hne : ¬ S' ≤ S := by
    intro hle
    apply hyS
    refine mem_normalizer_of_maps fun x hx => hle ⟨x, hx, rfl⟩
  have hle2 : S.relIndex S' ≤ 2 := hS ▸ relIndex_le_of_le_right hS'T (by rw [hS]; norm_num)
  have h0' : S.relIndex S' ≠ 0 := by
    intro h0'
    have := relIndex_mul_card (H := S) (K := S')
    rw [h0', zero_mul] at this
    exact Nat.card_pos.ne this
  have h1 : S.relIndex S' ≠ 1 := fun h => hne (relIndex_eq_one.1 h)
  have h2 : S.relIndex S' = 2 := by omega
  have := relIndex_mul_card (H := S) (K := S')
  rw [h2, card_map_conj'] at this
  exact this

omit [Finite G] in
theorem relIndex_sup_zpowers {T₁ : Subgroup G} [Finite G] {y : G}
    (hyN : y ∈ normalizer (T₁ : Set G)) (hyT : y ∉ T₁) (hy2 : y * y ∈ T₁) :
    T₁.relIndex (T₁ ⊔ zpowers y) = 2 := by
  have hdvd : T₁.relIndex (T₁ ⊔ zpowers y) ∣ 2 := by
    refine relIndex_dvd_two_iff.2 ⟨y⁻¹, inv_mem (mem_sup_right (mem_zpowers y)), fun b hb => ?_⟩
    rcases (mem_sup_zpowers_iff hyN hy2).1 hb with h | h
    · exact Or.inr h
    · exact Or.inl h
  have h1 : T₁.relIndex (T₁ ⊔ zpowers y) ≠ 1 := fun h =>
    hyT (relIndex_eq_one.1 h (mem_sup_right (mem_zpowers y)))
  have h0' : T₁.relIndex (T₁ ⊔ zpowers y) ≠ 0 := by
    intro h
    have := relIndex_mul_card (H := T₁) (K := T₁ ⊔ zpowers y)
    rw [h, zero_mul] at this
    exact Nat.card_pos.ne this
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd h h1
  · exact h

include h0 hι hSp hST hyN in
theorem l2C_of (hΦS : ∀ (g : G) (hg : g ∈ S), Φ.f ⟨g, hST hg⟩ = (e ⟨g, hg⟩).code)
    (hS : S.relIndex T₁ = 2) (hcardS : Nat.card S = 65536) (hyS : y ∉ normalizer (S : Set G))
    (hyT : y ∉ T₁) (hy2 : y * y ∈ T₁) {gs : List ℕ} {L : List (ℕ × ℕ × ℕ × ℕ)}
    (hK : kDataOK sMul 65536 (kInv sMul 65536) ι gs L = true) (hL : L.length = 64) :
    ∀ v ∈ T₁ ⊔ zpowers y, v ∉ T₁ → v * v = 1 →
      Nat.card ((T₁ ⊔ zpowers y) ⊓ centralizer ({v} : Set G) : Subgroup G) ≤ 2048 := by
  intro v hv hvT _
  set ΦS := sIso e
  set S' := S.map (MulAut.conj y).toMonoidHom
  set ιS := iotaS Φ h0 hι e hSp
  obtain ⟨hcardK, hspec⟩ := kData_spec ΦS sMul_zero_zero hK
  set K := (kSub ΦS gs).map S.subtype
  have hΦS' : ∀ x : S, Φ.f ⟨x, hST x.2⟩ = ΦS.f x := fun x => hΦS x x.2
  have hKS : K ≤ S ⊓ S' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    obtain ⟨c, hc, htab, -⟩ := hspec x hx hx1
    have hfi := f_iotaF Φ hι (SModel.codeIso.g c)
    have hcg : (SModel.codeIso.g c).code = c := SModel.codeIso.f_g hc
    rw [hcg, htab, ← hΦS'] at hfi
    have heq := Φ.inj hfi
    have hmem := iotaF_mem Φ h0 hι hSp (SModel.codeIso.g c)
    rw [heq] at hmem
    exact hmem
  have hKc : ∀ a : S, ((ιS a : S') : G) ∈ K → ((ιS a : S') : G) ≠ 1 →
      cInv S (ιS a : S') ≠ cInv S a := by
    intro a ha ha1
    obtain ⟨x, hx, hxa⟩ := ha
    have hx1 : x ≠ 1 := by
      rintro rfl; exact ha1 (by rw [← hxa]; rfl)
    obtain ⟨c, hc, htab, hcnt⟩ := hspec x hx hx1
    have hι1 : ι[(e a).code]! = ΦS.f x := by
      have h1 := f_iotaF Φ hι (e a)
      have h2 : (iotaF Φ (ι := ι) (e a) : G) = (x : G) := by rw [← iotaS_val]; exact hxa.symm
      have h3 : iotaF Φ (ι := ι) (e a) = ⟨x, hST x.2⟩ := Subtype.ext h2
      rw [h3, hΦS'] at h1
      exact h1.symm
    have hcode : c = (e a).code := iota_code_inj Φ h0 hι hc (e a).lt (by rw [htab, ← hι1])
    have hxS : ((ιS a : S') : G) = x := hxa.symm
    rw [show cInv S (ιS a : S') = cInv S x by rw [hxS], ← cInvC_eq ΦS sMul_zero_zero x,
      ← cInvC_eq ΦS sMul_zero_zero a]
    rw [show ΦS.f a = (e a).code from rfl, ← hcode]
    exact hcnt
  have hT := relIndex_sup_zpowers hyN hyT hy2
  have hvS := sPrime_map hST hS hyN hy2 hv hvT
  have hbound := card_centralizer_le ιS hKS hKc hS hT hvS
  have hD := card_inf_sPrime hST hyN hS hyS
  have hcK : Nat.card K = 64 := by
    rw [show Nat.card K = Nat.card (kSub ΦS gs) from card_map_of_injective Subtype.val_injective,
      hcardK, hL]
  rw [hcK] at hbound
  rw [hcardS] at hD
  omega

end CFSG.EvenSmallLie.OmegaEight.SpBranch

end
