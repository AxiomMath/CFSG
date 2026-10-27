module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57Gen
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.QuasithinUnique.Bridge.ThreeA7Excl

open CFSG.Quasithin CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
  CFSG.QuasithinUnique.B42A57 Equiv Equiv.Perm

variable {W : Type} [CommGroup W] [Finite W]

theorem exists_card_le_index_pow (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥)
    (hEel : IsElemAbelian2 E) (e : CQ L ≃* alternatingGroup (Fin 7)) :
    ∃ r : ℕ, Nat.card W ≤ (fixV E).index ^ r ∧ Nat.card E ^ r ≤ 2 ^ 6 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let cEquiv : Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) := MulEquiv.ofBijective _ hbij
  let φ : ↥(L ⊔ E) →* MulAut (alternatingGroup (Fin 7)) := actS hE e
  let ι : ↥E →* ↥(L ⊔ E) := Subgroup.inclusion le_sup_right
  let ε : ↥E →* Perm (Fin 7) := cEquiv.symm.toMonoidHom.comp (φ.comp ι)
  have hcε : ∀ b : ↥E, cEquiv (ε b) = φ (ι b) := fun b => cEquiv.apply_symm_apply _
  have hcf : ∀ s : alternatingGroup (Fin 7), cEquiv (s : Perm (Fin 7)) = MulAut.conj s :=
    fun s => MulAut.conjNormal_val
  have hεinj : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : φ (ι b) = 1 := by rw [← hcε, hb, map_one]
    obtain ⟨h3, h4⟩ := mem_center_of_actS_eq_one hW hperf hirr hE hEel e h1
    have hcomm : ∀ l ∈ L, l * (b : MulAut W) = (b : MulAut W) * l := fun l hl => by
      have := Subgroup.mem_center_iff.1 h4 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hodd := odd_orderOf_of_commutes hW hirr hcomm
    have hb2 : (b : MulAut W) ^ 2 = 1 := hEel.2 b b.2
    have hdvd : orderOf (b : MulAut W) ∣ 2 := orderOf_dvd_of_pow_eq_one hb2
    have h1' : orderOf (b : MulAut W) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subtype.ext (orderOf_eq_one_iff.1 h1')
  set B : Subgroup (Perm (Fin 7)) := ε.range with hB
  have hBcard : Nat.card B = Nat.card E :=
    (Nat.card_congr (MonoidHom.ofInjective hεinj).toEquiv).symm
  obtain ⟨b0, hb0⟩ : ∃ b0 : ↥E, b0 ≠ 1 := by
    by_contra h
    push Not at h
    apply hEne
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val (h ⟨x, hx⟩)
  have hB1 : B ≠ ⊥ := by
    intro h
    have hmem : ε b0 ∈ B := ⟨b0, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact hb0 (hεinj (hmem.trans (map_one ε).symm))
  have hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hEel.1 a a.2 b b.2)
  have hB2 : ∀ a ∈ B, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (by simpa [sq] using hEel.2 a a.2)
    rw [this, map_one]
  obtain ⟨r, f, hf, hcard, hcl⟩ := gen7 hB1 hBc hB2
  refine ⟨r, ?_, hBcard ▸ hcard⟩
  let cs : List (MulAut (alternatingGroup (Fin 7))) :=
    List.ofFn fun i => MulAut.conj (⟨f i, hf i⟩ : alternatingGroup (Fin 7))
  have hcs : ∀ c ∈ cs, c ∈ (actS hE e).range := by
    intro c hc
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    exact conj_mem_range_actS hE e _
  have hgen : ∀ s : alternatingGroup (Fin 7), MulAut.conj s ∈ Subgroup.closure
      {y : MulAut (alternatingGroup (Fin 7)) | ∃ c ∈ cs, ∃ b : ↥(L ⊔ E),
        (b : MulAut W) ∈ E ∧ y = c * actS hE e b * c⁻¹} := by
    intro s
    have h1 : (s : Perm (Fin 7)) ∈ Subgroup.closure
        {x | ∃ i, ∃ b ∈ B, x = f i * b * (f i)⁻¹} := hcl s.2
    have h2 := Subgroup.mem_map_of_mem cEquiv.toMonoidHom h1
    rw [MonoidHom.map_closure] at h2
    have h3 : cEquiv.toMonoidHom (s : Perm (Fin 7)) = MulAut.conj s := hcf s
    rw [h3] at h2
    refine Subgroup.closure_mono ?_ h2
    rintro _ ⟨x, ⟨i, b, ⟨b1, rfl⟩, rfl⟩, rfl⟩
    refine ⟨MulAut.conj (⟨f i, hf i⟩ : alternatingGroup (Fin 7)), ?_, ι b1, b1.2, ?_⟩
    · exact List.mem_ofFn.2 ⟨i, rfl⟩
    · have h4 : cEquiv (f i) = MulAut.conj (⟨f i, hf i⟩ : alternatingGroup (Fin 7)) :=
        hcf ⟨f i, hf i⟩
      show cEquiv (f i * ε b1 * (f i)⁻¹) = _
      rw [map_mul, map_mul, map_inv, h4, hcε]
  have := card_le_index_pow_of_inn_le hW hperf hirr hL hE hEel e cs hcs hgen
  rwa [List.length_ofFn] at this

theorem card_le_two_pow_six_of_offender (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L) (hL : L ≠ ⊥)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥)
    (hEel : IsElemAbelian2 E) (e : CQ L ≃* alternatingGroup (Fin 7))
    (hoff : Nat.card W ≤ Nat.card E * Nat.card (fixV E)) : Nat.card W ≤ 2 ^ 6 := by
  obtain ⟨r, h1, h2⟩ := exists_card_le_index_pow hW hperf hirr hL hE hEne hEel e
  have hidx : (fixV E).index ≤ Nat.card E := by
    have hmul := Subgroup.card_mul_index (fixV E)
    have hpos : 0 < Nat.card (fixV E) := Nat.card_pos
    by_contra hlt
    push Not at hlt
    have : Nat.card E * Nat.card (fixV E) < (fixV E).index * Nat.card (fixV E) :=
      Nat.mul_lt_mul_of_pos_right hlt hpos
    rw [mul_comm ((fixV E).index)] at this
    omega
  calc Nat.card W ≤ (fixV E).index ^ r := h1
    _ ≤ Nat.card E ^ r := Nat.pow_le_pow_left hidx r
    _ ≤ 2 ^ 6 := h2

end CFSG.QuasithinUnique.Bridge.ThreeA7Excl
