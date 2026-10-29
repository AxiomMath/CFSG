module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappers
public import CFSG.LargeExtraspecial.S7Perm

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace DSBS3

variable {G : Type} [Group G]

theorem cos_two {M A : Subgroup G} (h : M.relIndex A = 2) {a b : G}
    (ha : a ∈ A) (hb : b ∈ A) (ha' : a ∉ M) (hb' : b ∉ M) : a⁻¹ * b ∈ M := by
  have h2 : (M.subgroupOf A).index = 2 := h
  obtain ⟨c, hc⟩ := (Subgroup.index_eq_two_iff' (H := M.subgroupOf A)).mp h2
  have key : ∀ x : G, ∀ hx : x ∈ A, x ∉ M → (c : G) * x ∈ M := by
    intro x hx hxM
    have h1 := hc ⟨x, hx⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mk] at h1
    rcases h1 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hxM
  have e : a⁻¹ * b = ((c : G) * a)⁻¹ * ((c : G) * b) := by group
  rw [e]
  exact M.mul_mem (M.inv_mem (key a ha ha')) (key b hb hb')

theorem two_pow_dvd_six {m a : ℕ} (h1 : m ∣ 2 ^ a) (h2 : m ∣ 6) (hm : m ≠ 1) : m = 2 := by
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  rcases j with _ | _ | j
  · exact absurd (pow_zero 2) hm
  · rfl
  · exfalso
    have h4 : 2 ^ 2 ∣ 2 ^ (j + 1 + 1) := pow_dvd_pow 2 (by omega)
    have h5 := h4.trans h2
    norm_num at h5

theorem mem_normalizer_of_conj {H P : Subgroup G} (hP : ∀ g ∈ P, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    P ≤ Subgroup.normalizer (H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hP g hg x, fun hx => ?_⟩
  have h := hP g⁻¹ (P.inv_mem hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rw [e] at h
  exact h

theorem mem_centMod {P L Q : Subgroup G} {p : G} :
    p ∈ dsCentMod P L Q ↔ p ∈ P ∧ p ∈ Subgroup.normalizer (Q : Set G) ∧ ∀ l ∈ L, ⁅p, l⁆ ∈ Q :=
  Iff.rfl

@[expose] noncomputable def psS3 (L : Subgroup G) (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) :
    ↥L →* Equiv.Perm (Fin 3) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥L))

instance pCore_normal_subgroup (L : Subgroup G) : (pCore 2 ↥L).Normal :=
  CFSG.LieType.BorelTits.pCore_normal 2

theorem psS3_apply (L : Subgroup G) (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) (x : ↥L) :
    psS3 L e x = e (QuotientGroup.mk x) := by
  show e (QuotientGroup.mk' (pCore 2 ↥L) x) = _
  rfl

theorem psS3_eq_one_iff (L : Subgroup G) (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) (x : ↥L) :
    psS3 L e x = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
  rw [psS3_apply, map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff, F1.mem_pCore_iff_coe]

theorem psS3_surj (L : Subgroup G) (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) :
    Function.Surjective (psS3 L e) := by
  intro σ
  obtain ⟨q, rfl⟩ := e.surjective σ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥L) q
  exact ⟨x, rfl⟩

@[expose] def conjSubHom (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) : ↥L →* ↥L where
  toFun x := ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x.1).mp x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] theorem conjSubHom_coe {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : ((conjSubHom L g hg x : ↥L) : G) = g * x * g⁻¹ := by
  unfold conjSubHom
  rfl

theorem psS3_conj (L : Subgroup G) (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgN : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G)) :
    ∃ τ : Equiv.Perm (Fin 3), ∀ x : ↥L,
      psS3 L e (conjSubHom L g hgL x) = τ * psS3 L e x * τ⁻¹ := by
  have hker : pCore 2 ↥L ≤ ((psS3 L e).comp (conjSubHom L g hgL)).ker := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, psS3_eq_one_iff]
    have hy' : (y : G) ∈ pCoreOf 2 L := (F1.mem_pCore_iff_coe y).mp hy
    exact (Subgroup.mem_normalizer_iff.mp hgN _).mp hy'
  let φ : oTwoQuot ↥L →* Equiv.Perm (Fin 3) :=
    QuotientGroup.lift (pCore 2 ↥L) ((psS3 L e).comp (conjSubHom L g hgL)) hker
  let f : Equiv.Perm (Fin 3) →* Equiv.Perm (Fin 3) := φ.comp e.symm.toMonoidHom
  have hf : ∀ x : ↥L, f (psS3 L e x) = psS3 L e (conjSubHom L g hgL x) := by
    intro x
    show φ (e.symm (psS3 L e x)) = _
    rw [psS3_apply, MulEquiv.symm_apply_apply]
    exact QuotientGroup.lift_mk _ _ x
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨x, rfl⟩ := psS3_surj L e σ
    rw [hf x, psS3_eq_one_iff] at hσ
    rw [psS3_eq_one_iff]
    have hinv : g⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      (Subgroup.normalizer (pCoreOf 2 L : Set G)).inv_mem hgN
    have h2 := (Subgroup.mem_normalizer_iff.mp hinv) (g * x * g⁻¹)
    have h3 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = (x : G) := by group
    rw [h3] at h2
    exact h2.mp hσ
  obtain ⟨τ, hτ⟩ := CFSG.LargeExtraspecial.S7.perm_three_exists_conj f hinj
  refine ⟨τ, fun x => ?_⟩
  rw [← hf x]
  exact hτ _

theorem relIndex_pCoreOf (L : Subgroup G) (e : oTwoQuot ↥L ≃* Equiv.Perm (Fin 3)) :
    (pCoreOf 2 L).relIndex L = 6 := by
  have h1 : (pCoreOf 2 L).subgroupOf L = pCore 2 ↥L := by
    ext x
    rw [Subgroup.mem_subgroupOf, F1.mem_pCore_iff_coe]
  show ((pCoreOf 2 L).subgroupOf L).index = 6
  rw [h1, Subgroup.index_eq_card]
  show Nat.card (oTwoQuot ↥L) = 6
  rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end DSBS3

open DSBS3

theorem leafDSBS3Vertex [DSLeaf LeafDSBA5Vertex] [DSLeaf LeafSylowS] [DSLeaf LeafFrattiniFaithful] [DSLeaf LeafFrattiniChief] [DSLeaf LeafM7] [DSLeaf LeafRankBounds] : LeafDSBS3Vertex := by
  intro G _ _ L1 L2 S h
  obtain ⟨e⟩ := h.s3
  have H2 : Hyp111R L2 L1 S := h.hyp.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := L2 ⊔ bigB L2 L1 S with hPdef
  set Q : Subgroup G := pCoreOf 2 P with hQdef
  set N : Subgroup G := pCoreOf 2 L2 with hNdef
  set B : Subgroup G := bigB L2 L1 S with hBdef
  set C : Subgroup G := dsCentMod P L2 Q with hCdef
  have hS := sylow_s H2
  have hS1 := sylow_s h.hyp
  have hSyl : IsSylowTwoOf S P := hS.2.1
  have hSP : S ≤ P := hSyl.1
  have hS2 : IsPGroup 2 S := hSyl.2.1
  have hQS : Q ≤ S := hS.2.2
  have hLP : L2 ≤ P := le_sup_left
  have hBP : B ≤ P := le_sup_right
  have hPN : P ≤ Subgroup.normalizer (L2 : Set G) := F1.parabolic_le_normalizer H2
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P
  have hQP : Q ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hQnorm : ∀ g ∈ P, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := fun g hg q hq =>
    (Subgroup.mem_normalizer_iff.mp (hPQ hg) q).mp hq
  have hNQ : N = Q ⊓ L2 := (F1.inf_pCoreOf_parabolic_eq H2).symm
  have hNQ' : N ≤ Q := by rw [hNQ]; exact inf_le_left
  have hNL2 : N ≤ L2 := by rw [hNQ]; exact inf_le_right
  have hNnorm : ∀ g ∈ P, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
    intro g hg x hx
    rw [hNQ] at hx ⊢
    exact ⟨hQnorm g hg x hx.1, (Subgroup.mem_normalizer_iff.mp (hPN hg) x).mp hx.2⟩
  have hgNN : P ≤ Subgroup.normalizer (N : Set G) := mem_normalizer_of_conj hNnorm
  set ψ := psS3 L2 e with hψdef
  have hψsurj : Function.Surjective ψ := psS3_surj L2 e
  have hψker : ∀ x : ↥L2, ψ x = 1 ↔ (x : G) ∈ N := fun x => psS3_eq_one_iff L2 e x
  have hconj : ∀ g ∈ P, ∃ τ : Equiv.Perm (Fin 3), ∀ (x : ↥L2)
      (hg' : g ∈ Subgroup.normalizer (L2 : Set G)),
      ψ (conjSubHom L2 g hg' x) = τ * ψ x * τ⁻¹ := by
    intro g hg
    obtain ⟨τ, hτ⟩ := psS3_conj L2 e (hPN hg) (hgNN hg)
    exact ⟨τ, fun x _ => hτ x⟩
  have hNidx : N.relIndex L2 = 6 := relIndex_pCoreOf L2 e
  have hCP : C ≤ P := fun c hc => (mem_centMod.mp hc).1
  have hCnorm : ∀ g ∈ P, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hc
    obtain ⟨hcP, -, hcL⟩ := mem_centMod.mp hc
    have hgP' : g * c * g⁻¹ ∈ P := P.mul_mem (P.mul_mem hg hcP) (P.inv_mem hg)
    refine mem_centMod.mpr ⟨hgP', hPQ hgP', fun l hl => ?_⟩
    have hm : g⁻¹ * l * g⁻¹⁻¹ ∈ L2 :=
      (Subgroup.mem_normalizer_iff.mp (hPN (P.inv_mem hg)) l).mp hl
    have e1 : ⁅g * c * g⁻¹, l⁆ = g * ⁅c, g⁻¹ * l * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact hQnorm g hg _ (hcL _ hm)
  have hQC : Q ≤ C := by
    intro q hq
    refine mem_centMod.mpr ⟨hQP hq, hPQ (hQP hq), fun l hl => ?_⟩
    have e1 : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact Q.mul_mem hq (hQnorm l (hLP hl) q⁻¹ (Q.inv_mem hq))
  have hdecomp : ∀ p ∈ P, ∃ l ∈ L2, ∃ c ∈ C, p = l * c := by
    intro p hp
    obtain ⟨τ, hτ⟩ := hconj p hp
    obtain ⟨y, hy⟩ := hψsurj τ
    refine ⟨(y : G), y.2, (y : G)⁻¹ * p, ?_, by group⟩
    refine mem_centMod.mpr ⟨P.mul_mem (P.inv_mem (hLP y.2)) hp,
      hPQ (P.mul_mem (P.inv_mem (hLP y.2)) hp), fun x hx => ?_⟩
    have hZ : ψ (y⁻¹ * conjSubHom L2 p (hPN hp) ⟨x, hx⟩ * y * (⟨x, hx⟩ : ↥L2)⁻¹) = 1 := by
      simp only [map_mul, map_inv, hy, hτ]
      group
    have hZN := (hψker _).mp hZ
    have e1 : ⁅(y : G)⁻¹ * p, x⁆ =
        ((y⁻¹ * conjSubHom L2 p (hPN hp) ⟨x, hx⟩ * y * (⟨x, hx⟩ : ↥L2)⁻¹ : ↥L2) : G) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, conjSubHom_coe]
      group
    rw [e1]
    exact hNQ' hZN
  have hL2C : L2 ⊓ C = N := by
    apply le_antisymm
    · intro l hl
      obtain ⟨hlL, hlC⟩ := hl
      have hcomm : ∀ σ : Equiv.Perm (Fin 3), ψ ⟨l, hlL⟩ * σ = σ * ψ ⟨l, hlL⟩ := by
        intro σ
        obtain ⟨x, rfl⟩ := hψsurj σ
        have hk : l * (x : G) * l⁻¹ * (x : G)⁻¹ ∈ N := by
          rw [hNQ]
          exact ⟨(mem_centMod.mp hlC).2.2 x x.2,
            L2.mul_mem (L2.mul_mem (L2.mul_mem hlL x.2) (L2.inv_mem hlL)) (L2.inv_mem x.2)⟩
        have hk' : ψ (⟨l, hlL⟩ * x * (⟨l, hlL⟩ : ↥L2)⁻¹ * x⁻¹) = 1 := (hψker _).mpr hk
        simp only [map_mul, map_inv] at hk'
        calc ψ ⟨l, hlL⟩ * ψ x
            = (ψ ⟨l, hlL⟩ * ψ x * (ψ ⟨l, hlL⟩)⁻¹ * (ψ x)⁻¹) * (ψ x * ψ ⟨l, hlL⟩) := by group
          _ = ψ x * ψ ⟨l, hlL⟩ := by rw [hk', one_mul]
      have h1 : ψ ⟨l, hlL⟩ = 1 := CFSG.LargeExtraspecial.S7.perm_three_eq_one_of_comm _ hcomm
      exact (hψker _).mp h1
    · exact le_inf hNL2 (hNQ'.trans hQC)
  have hBS : B ≤ Subgroup.normalizer (S : Set G) := by
    rw [hBdef, bigB_comm L1 L2 S]
    exact DSBHyp.bnorm h
  have hLe : ∀ l ∈ L2, ∀ x ∈ S ⊓ C, l * x * l⁻¹ ∈ S ⊓ C := by
    intro l hl x hx
    obtain ⟨hxS, hxC⟩ := hx
    have hxL : ⁅x, l⁆ ∈ Q := (mem_centMod.mp hxC).2.2 l hl
    have hq : ⁅l, x⁆ ∈ Q := by
      have e1 : ⁅l, x⁆ = ⁅x, l⁆⁻¹ := by simp only [commutatorElement_def]; group
      rw [e1]
      exact Q.inv_mem hxL
    have e2 : l * x * l⁻¹ = ⁅l, x⁆ * x := by simp only [commutatorElement_def]; group
    rw [e2]
    exact ⟨S.mul_mem (hQS hq) hxS, C.mul_mem (hQC hq) hxC⟩
  have hBT : ∀ b ∈ B, ∀ x ∈ S ⊓ C, b * x * b⁻¹ ∈ S ⊓ C := by
    intro b hb x hx
    obtain ⟨hxS, hxC⟩ := hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hBS hb) x).mp hxS, hCnorm b (hBP hb) x hxC⟩
  have hTP : S ⊓ C ≤ P := inf_le_left.trans hSP
  have hPT : P ≤ Subgroup.normalizer ((S ⊓ C : Subgroup G) : Set G) :=
    sup_le (mem_normalizer_of_conj hLe) (mem_normalizer_of_conj hBT)
  have hTpg : IsPGroup 2 ↥(S ⊓ C) := hS2.to_le inf_le_left
  have hTQ : S ⊓ C ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTP hPT hTpg
  have hT : S ⊓ C = Q := le_antisymm hTQ (le_inf hQS hQC)
  have hsup : L2 ⊔ C = P := le_antisymm (sup_le hLP hCP) (fun p hp => by
    obtain ⟨l, hl, c, hc, rfl⟩ := hdecomp p hp
    exact (L2 ⊔ C).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right hc))
  have hL2N : L2 ≤ Subgroup.normalizer (C : Set G) :=
    mem_normalizer_of_conj (fun g hg c hc => hCnorm g (hLP hg) c hc)
  have hCP6 : C.relIndex P = 6 := by
    rw [← hsup, F1.relIndex_sup_eq_of_le_normalizer hL2N, ← Subgroup.inf_relIndex_right, inf_comm,
      hL2C, hNidx]
  have hSN : S ≤ Subgroup.normalizer (C : Set G) :=
    mem_normalizer_of_conj (fun g hg c hc => hCnorm g (hSP hg) c hc)
  have hCS : C.relIndex S = Q.relIndex S := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hT]
  have hCSC : C.relIndex (S ⊔ C) = C.relIndex S := F1.relIndex_sup_eq_of_le_normalizer hSN
  have hdvd6 : C.relIndex (S ⊔ C) ∣ 6 := by
    have h6 := Subgroup.relIndex_mul_relIndex (H := C) (K := S ⊔ C) (L := P) le_sup_right
      (sup_le hSP hCP)
    rw [hCP6] at h6
    exact Dvd.intro _ h6
  have hQidx : Q.relIndex S * Nat.card Q = Nat.card S := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := S)
    rwa [inf_eq_left.mpr hQS] at h
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS2
  have hdvdS : Q.relIndex S ∣ 2 ^ a := by
    rw [← ha]
    exact Dvd.intro _ hQidx
  have hS₂sylow : IsSylowTwoOf (S ⊓ L2) L2 := H2.hyp.h1.sylow
  have hNS₂ : N ≤ S ⊓ L2 := F7.isSylowTwoOf_pCoreOf_le hS₂sylow
  have hS₂N : S ⊓ L2 ≠ N := by
    intro heq
    apply hS₂sylow.2.2
    have h6 : ((S ⊓ L2).subgroupOf L2).index = 6 := by
      rw [heq]
      exact hNidx
    rw [h6]
    norm_num
  have hN2 : N.relIndex (S ⊓ L2) = 2 := by
    have hdvd : N.relIndex (S ⊓ L2) ∣ 6 := by
      have h := Subgroup.relIndex_mul_relIndex (H := N) (K := S ⊓ L2) (L := L2) hNS₂ inf_le_right
      rw [hNidx] at h
      exact Dvd.intro _ h
    obtain ⟨a₂, ha₂⟩ := IsPGroup.iff_card.mp (hS2.to_le (inf_le_left : S ⊓ L2 ≤ S))
    have hpow : N.relIndex (S ⊓ L2) ∣ 2 ^ a₂ := by
      have h := Subgroup.relIndex_mul_card (H := N) (K := S ⊓ L2)
      rw [inf_eq_left.mpr hNS₂] at h
      rw [← ha₂]
      exact Dvd.intro _ h
    apply two_pow_dvd_six hpow hdvd
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hS₂N (le_antisymm h1 hNS₂)
  obtain ⟨t, htS2, htN⟩ : ∃ t ∈ S ⊓ L2, t ∉ N := by
    by_contra hcon
    push Not at hcon
    exact hS₂N (le_antisymm (fun x hx => hcon x hx) hNS₂)
  have htL : t ∈ L2 := htS2.2
  have htS : t ∈ S := htS2.1
  have hsq : t ^ 2 ∈ N := by
    by_contra hc
    apply htN
    have h1 := cos_two hN2 htS2 (pow_mem htS2 2) htN hc
    have e1 : t⁻¹ * t ^ 2 = t := by group
    rwa [e1] at h1
  have hτ₀ne : ψ ⟨t, htL⟩ ≠ 1 := fun h1 => htN ((hψker ⟨t, htL⟩).mp h1)
  have hτ₀sq : ψ ⟨t, htL⟩ * ψ ⟨t, htL⟩ = 1 := by
    rw [← map_mul]
    apply (hψker _).mpr
    show t * t ∈ N
    rw [← pow_two]
    exact hsq
  have hG3 : ∀ d ∈ borelOf L1 S, orderOf d = 3 → ∀ l ∈ L2, ⁅d, l⁆ ∈ Q := by
    intro d hd hd3 l hl
    have hdB : borelOf L1 S ≤ B := le_sup_right.trans le_sup_left
    have hdP : d ∈ P := hBP (hdB hd)
    have hdS2 : d ∈ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
      F1.borelOf_le_normalizer_sylow H2 hd
    have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
    obtain ⟨τ, hτ⟩ := hconj d hdP
    have hu_S2 : d * t * d⁻¹ ∈ S ⊓ L2 := (Subgroup.mem_normalizer_iff.mp hdS2 t).mp htS2
    have hu_ne : d * t * d⁻¹ ∉ N := fun hm =>
      htN ((Subgroup.mem_normalizer_iff.mp (hgNN hdP) t).mpr hm)
    have hcos : t⁻¹ * (d * t * d⁻¹) ∈ N := cos_two hN2 htS2 hu_S2 htN hu_ne
    have hψu : ψ (conjSubHom L2 d (hPN hdP) ⟨t, htL⟩) = ψ ⟨t, htL⟩ := by
      have hK : ψ ((⟨t, htL⟩ : ↥L2)⁻¹ * conjSubHom L2 d (hPN hdP) ⟨t, htL⟩) = 1 :=
        (hψker _).mpr hcos
      rw [map_mul, map_inv, inv_mul_eq_one] at hK
      exact hK.symm
    have hτeq : τ * ψ ⟨t, htL⟩ = ψ ⟨t, htL⟩ * τ := by
      have h1 := hτ ⟨t, htL⟩ (hPN hdP)
      rw [hψu] at h1
      have h2 : τ * ψ ⟨t, htL⟩ * τ⁻¹ = ψ ⟨t, htL⟩ := h1.symm
      calc τ * ψ ⟨t, htL⟩ = τ * ψ ⟨t, htL⟩ * τ⁻¹ * τ := by group
        _ = ψ ⟨t, htL⟩ * τ := by rw [h2]
    rcases CFSG.LargeExtraspecial.S7.perm_three_eq_of_comm_inv τ _ hτ₀sq hτ₀ne hτeq with
      hτ1 | hτ2
    ·
      have hψ1 : ψ (conjSubHom L2 d (hPN hdP) ⟨l, hl⟩) = ψ ⟨l, hl⟩ := by
        rw [hτ ⟨l, hl⟩ (hPN hdP), hτ1, one_mul, inv_one, mul_one]
      have hK : ψ (conjSubHom L2 d (hPN hdP) ⟨l, hl⟩ * (⟨l, hl⟩ : ↥L2)⁻¹) = 1 := by
        rw [map_mul, map_inv, hψ1, mul_inv_cancel]
      have hmem := (hψker _).mp hK
      have e1 : ((conjSubHom L2 d (hPN hdP) ⟨l, hl⟩ * (⟨l, hl⟩ : ↥L2)⁻¹ : ↥L2) : G) =
          ⁅d, l⁆ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjSubHom_coe, commutatorElement_def]
      rw [e1] at hmem
      exact hNQ' hmem
    ·
      exfalso
      have hpP : t⁻¹ * d ∈ P := P.mul_mem (P.inv_mem (hLP htL)) hdP
      have hpC : t⁻¹ * d ∈ C := by
        refine mem_centMod.mpr ⟨hpP, hPQ hpP, fun x hx => ?_⟩
        have hZ : ψ ((⟨t, htL⟩ : ↥L2)⁻¹ * conjSubHom L2 d (hPN hdP) ⟨x, hx⟩ * ⟨t, htL⟩ *
            (⟨x, hx⟩ : ↥L2)⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [hτ ⟨x, hx⟩ (hPN hdP), hτ2]
          group
        have hZN := (hψker _).mp hZ
        have e1 : ⁅t⁻¹ * d, x⁆ = (((⟨t, htL⟩ : ↥L2)⁻¹ * conjSubHom L2 d (hPN hdP) ⟨x, hx⟩ *
            ⟨t, htL⟩ * (⟨x, hx⟩ : ↥L2)⁻¹ : ↥L2) : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjSubHom_coe, commutatorElement_def,
            Subgroup.coe_mk]
          group
        rw [e1]
        exact hNQ' hZN
      have e2 : d ^ 2 = t ^ 2 * (t⁻¹ * (t⁻¹ * d) * t) * (t⁻¹ * d) := by rw [pow_two]; group
      have hm1 : t ^ 2 ∈ C := hQC (hNQ' hsq)
      have hm2 : t⁻¹ * (t⁻¹ * d) * t ∈ C := by
        have e3 : t⁻¹ * (t⁻¹ * d) * t = t⁻¹ * (t⁻¹ * d) * (t⁻¹)⁻¹ := by rw [inv_inv]
        rw [e3]
        exact hCnorm t⁻¹ (P.inv_mem (hLP htL)) _ hpC
      have hd2 : d ^ 2 ∈ C := by
        rw [e2]
        exact C.mul_mem (C.mul_mem hm1 hm2) hpC
      have h3 : d ^ 2 * d = 1 := by
        rw [← pow_succ]
        exact hd3'
      have hdC : d ∈ C := by
        have h4 := C.inv_mem hd2
        rwa [inv_eq_of_mul_eq_one_right h3] at h4
      have htC : t ∈ C := by
        have e4 : t = d * (t⁻¹ * d)⁻¹ := by group
        rw [e4]
        exact C.mul_mem hdC (C.inv_mem hpC)
      have htN' : t ∈ L2 ⊓ C := ⟨htL, htC⟩
      rw [hL2C] at htN'
      exact htN htN'
  have hQS1 : Q.relIndex S ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    apply htN
    rw [hNQ]
    exact ⟨h1 htS, htL⟩
  have hdvd6' : Q.relIndex S ∣ 6 := by
    rw [← hCS, ← hCSC]
    exact hdvd6
  have hQS2 : Q.relIndex S = 2 := two_pow_dvd_six hdvdS hdvd6' hQS1
  have hS2Q : Q ⊓ (S ⊓ L2) = N := by
    apply le_antisymm
    · intro x hx
      rw [hNQ]
      exact ⟨hx.1, hx.2.2⟩
    · intro x hx
      exact ⟨hNQ' hx, hNS₂ hx⟩
  have hS2Qidx : Q.relIndex (S ⊓ L2 ⊔ Q) = 2 := by
    have hS2N' : S ⊓ L2 ≤ Subgroup.normalizer (Q : Set G) := fun x hx => hPQ (hSP hx.1)
    rw [F1.relIndex_sup_eq_of_le_normalizer hS2N', ← Subgroup.inf_relIndex_right, hS2Q, hN2]
  have hG1 : S = S ⊓ L2 ⊔ Q := by
    have h1 := Subgroup.relIndex_mul_relIndex (H := Q) (K := S ⊓ L2 ⊔ Q) (L := S) le_sup_right
      (sup_le inf_le_left hQS)
    rw [hS2Qidx, hQS2] at h1
    have h2 : (S ⊓ L2 ⊔ Q).relIndex S = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) (sup_le inf_le_left hQS)
  have hG4 : Nat.card Q = 2 * Nat.card (dsQ L1 L2 S) := by
    have hA := dsba5_vertex h
    have hQ1S : dsQ L1 L2 S ≤ S := hS1.2.2
    have hQ1idx : (dsQ L1 L2 S).relIndex S * Nat.card (dsQ L1 L2 S) = Nat.card S := by
      have h1 := Subgroup.relIndex_mul_card (H := dsQ L1 L2 S) (K := S)
      rwa [inf_eq_left.mpr hQ1S] at h1
    rw [hA.2.1] at hQ1idx
    rw [hQS2] at hQidx
    omega
  exact ⟨hG1, hQS2, fun d hd hd3 l hl => hG3 d hd hd3 l hl, hG4⟩

end CFSG.GH74.QTGen4.DSGen4
