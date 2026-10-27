module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.General
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin Matrix MatrixGroups

section Generic

variable {G : Type*} [Group G]

theorem isSylowTwoOf_of_le_of_le {P C A : Subgroup G} (hP : IsSylowTwoOf P A) (hPC : P ≤ C)
    (hCA : C ≤ A) : IsSylowTwoOf P C := by
  refine ⟨hPC, hP.isPGroup, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P C A hPC hCA
  have h2 : 2 ∣ P.relIndex A := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem mem_of_isSylowTwoOf_of_le_normalizer [Finite G] {P C : Subgroup G}
    (hP : IsSylowTwoOf P C) (hn : C ≤ Subgroup.normalizer (P : Set G)) {w : G} (hwC : w ∈ C)
    (hw : ∃ k : ℕ, w ^ 2 ^ k = 1) : w ∈ P := by
  have h2 : IsPGroup 2 (Subgroup.zpowers w) := by
    obtain ⟨k, hk⟩ := hw
    have hdvd : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  obtain ⟨Q, hwQ, hQ⟩ := exists_isSylowTwoOf_of_le (Subgroup.zpowers_le.mpr hwC) h2
  obtain ⟨h, hh, hQeq⟩ := hP.exists_conj hQ
  have hPeq : P.map (MulAut.conj h).toMonoidHom = P := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hn hh) y).mp hy
    · intro x hx
      refine ⟨h⁻¹ * x * h, ?_, by simp [MulAut.conj_apply]; group⟩
      have := (Subgroup.mem_normalizer_iff.mp (hn (C.inv_mem hh)) x).mp hx
      simpa using this
  rw [hPeq] at hQeq
  have hwQ' : w ∈ Q := hwQ (Subgroup.mem_zpowers w)
  rwa [hQeq] at hwQ'

theorem mem_normalizer_of_mem_normalizer_subgroupOf {A P : Subgroup G} (hPA : P ≤ A) {a : A}
    (h : a ∈ Subgroup.normalizer ((P.subgroupOf A : Subgroup A) : Set A)) :
    (a : G) ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  constructor
  · intro hy
    have := (h ⟨y, hPA hy⟩).mp hy
    exact this
  · intro hy
    have hyA : y ∈ A := by
      have h1 : (a : G) * y * (a : G)⁻¹ ∈ A := hPA hy
      have h2 := A.mul_mem (A.mul_mem (A.inv_mem a.2) h1) a.2
      simpa [mul_assoc] using h2
    exact (h ⟨y, hyA⟩).mpr hy

end Generic

section LemmaG

theorem le_normalizer_of_surjective_sl2 {A : Type*} [Group A] {F : Type*} [Field F] [Fintype F]
    {m : ℕ} (hF : Fintype.card F = 2 ^ m) (hm : 0 < m) (α : A →* SL(2, F))
    (hα : Function.Surjective α) {P X : Subgroup A} (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    (hker : α.ker ≤ P) (hPX : P ≤ X) (hX : X ≠ ⊤) :
    X ≤ Subgroup.normalizer (P : Set A) := by
  have hmem : ∀ y : A, y ∈ P ↔ α y ∈ P.map α := by
    intro y
    constructor
    · exact fun hy => Subgroup.mem_map_of_mem α hy
    · rintro ⟨z, hz, hzy⟩
      have h1 : z⁻¹ * y ∈ α.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hzy, inv_mul_cancel]
      have h2 : z⁻¹ * y ∈ P := hker h1
      have := P.mul_mem hz h2
      simpa using this
  have hPsyl : IsSylowTwoOf (P.map α) ⊤ := by
    refine ⟨le_top, hP2.map α, ?_⟩
    show ¬ 2 ∣ (P.map α).relIndex ⊤
    rw [Subgroup.relIndex_top_right, Subgroup.index_map_eq P hα hker]
    exact hPidx
  rcases dicksonLite hF hm hPsyl (Subgroup.map_mono hPX) with htop | hN
  · exfalso
    apply hX
    rw [eq_top_iff]
    intro a _
    have ha : α a ∈ X.map α := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨x, hx, hxa⟩ := ha
    have h1 : x⁻¹ * a ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxa, inv_mul_cancel]
    have := X.mul_mem hx (hPX (hker h1))
    simpa using this
  · intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_map_of_mem α hx)) (α y)
    rw [hmem y, hmem (x * y * x⁻¹), h1]
    simp [map_mul, map_inv]

end LemmaG

section Ambient

variable {G : Type*} [Group G]

theorem inf_le_normalizer_of_isLin2Type {A P X : Subgroup G} {n : ℕ} (hn : 0 < n)
    (hlin : IsLin2Type A n) (hP : IsSylowTwoOf P A) (hPX : P ≤ X) (hAX : ¬ A ≤ X) :
    A ⊓ X ≤ Subgroup.normalizer (P : Set G) := by
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαker, -⟩ := hlin
  have hP2 : IsPGroup 2 (P.subgroupOf A) :=
    hP.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hP.le).symm
  have hker : α.ker ≤ P.subgroupOf A := by
    rw [hαker]
    intro z hz
    have hz' : (z : G) ∈ pCoreOf 2 A := ⟨z, by assumption, rfl⟩
    exact hP.pCoreOf_le hz'
  have hX : X.subgroupOf A ≠ ⊤ := fun h => hAX (Subgroup.subgroupOf_eq_top.mp h)
  have hPX' : P.subgroupOf A ≤ X.subgroupOf A := fun y hy => hPX hy
  have key := le_normalizer_of_surjective_sl2 hcard hn α hαs hP2 hP.2.2 hker hPX' hX
  intro x hx
  exact mem_normalizer_of_mem_normalizer_subgroupOf hP.le (a := ⟨x, hx.1⟩) (key hx.2)

end Ambient

section Commuting

variable {G : Type*} [Group G] [Finite G]

theorem isSylowTwoOf_sup_of_commuting {A B P₁ P₂ : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hP₁ : IsSylowTwoOf P₁ A) (hP₂ : IsSylowTwoOf P₂ B)
    (hinf : A ⊓ B ≤ P₁ ⊓ P₂) : IsSylowTwoOf (P₁ ⊔ P₂) (A ⊔ B) := by
  have hAB' : B ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_commute hAB
  have hPP : P₂ ≤ Subgroup.normalizer (P₁ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => hAB a (hP₁.le ha) b (hP₂.le hb)
  have h1 := card_sup_mul_card_inf (A := B) (B := A) hAB'
  have h2 := card_sup_mul_card_inf (A := P₂) (B := P₁) hPP
  have hinfeq : A ⊓ B = P₁ ⊓ P₂ := le_antisymm hinf (inf_le_inf hP₁.le hP₂.le)
  rw [sup_comm, inf_comm, hinfeq] at h1
  rw [sup_comm, inf_comm] at h2
  have hA : P₁.relIndex A * Nat.card P₁ = Nat.card A := by
    have := Subgroup.relIndex_mul_card (H := P₁) (K := A)
    rwa [inf_eq_left.mpr hP₁.le] at this
  have hB : P₂.relIndex B * Nat.card P₂ = Nat.card B := by
    have := Subgroup.relIndex_mul_card (H := P₂) (K := B)
    rwa [inf_eq_left.mpr hP₂.le] at this
  have hQle : P₁ ⊔ P₂ ≤ A ⊔ B := sup_le_sup hP₁.le hP₂.le
  have hQ : (P₁ ⊔ P₂).relIndex (A ⊔ B) * Nat.card (P₁ ⊔ P₂ : Subgroup G) =
      Nat.card (A ⊔ B : Subgroup G) := by
    have := Subgroup.relIndex_mul_card (H := P₁ ⊔ P₂) (K := A ⊔ B)
    rwa [inf_eq_left.mpr hQle] at this
  have hc : 0 < Nat.card (P₁ ⊓ P₂ : Subgroup G) := Nat.card_pos
  have hQpos : 0 < Nat.card (P₁ ⊔ P₂ : Subgroup G) := Nat.card_pos
  have hrel : (P₁ ⊔ P₂).relIndex (A ⊔ B) = P₁.relIndex A * P₂.relIndex B := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hQpos hc)
    calc (P₁ ⊔ P₂).relIndex (A ⊔ B) * (Nat.card (P₁ ⊔ P₂ : Subgroup G) *
          Nat.card (P₁ ⊓ P₂ : Subgroup G))
        = Nat.card (A ⊔ B : Subgroup G) * Nat.card (P₁ ⊓ P₂ : Subgroup G) := by
          rw [← hQ]; ring
      _ = Nat.card A * Nat.card B := by rw [h1, mul_comm]
      _ = P₁.relIndex A * P₂.relIndex B * (Nat.card (P₁ ⊔ P₂ : Subgroup G) *
            Nat.card (P₁ ⊓ P₂ : Subgroup G)) := by
          rw [← hA, ← hB, h2]
          ring
  refine ⟨hQle, hP₁.isPGroup.to_sup_of_normal_left' hP₂.isPGroup hPP, fun hdvd => ?_⟩
  have hdvd' : 2 ∣ P₁.relIndex A * P₂.relIndex B := by rw [← hrel]; exact hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd' with h | h
  · exact hP₁.2.2 h
  · exact hP₂.2.2 h

theorem conj_mem_of_commuting {A B P X : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hP : IsSylowTwoOf P A) (hPX : P ≤ X) (hAX : A ⊓ X ≤ Subgroup.normalizer (P : Set G))
    {k : G} (hk : k ∈ A ⊔ B) (hkX : k ∈ X) {p : G} (hp : p ∈ P) : k * p * k⁻¹ ∈ P := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer
    (le_normalizer_of_commute hAB)).mp hk
  have hpA : p ∈ A := hP.le hp
  have hbp : b * p = p * b := (hAB p hpA b hb).symm
  have e : a * b * p * (a * b)⁻¹ = a * p * a⁻¹ := by
    calc a * b * p * (a * b)⁻¹ = a * (b * p) * b⁻¹ * a⁻¹ := by group
      _ = a * (p * b) * b⁻¹ * a⁻¹ := by rw [hbp]
      _ = a * p * a⁻¹ := by group
  rw [e]
  have hxA : a * p * a⁻¹ ∈ A := A.mul_mem (A.mul_mem ha hpA) (A.inv_mem ha)
  have hxX : a * p * a⁻¹ ∈ X := by rw [← e]; exact X.mul_mem (X.mul_mem hkX (hPX hp)) (X.inv_mem hkX)
  have h2 : ∃ e : ℕ, (a * p * a⁻¹) ^ 2 ^ e = 1 := by
    obtain ⟨e, he⟩ := hP.isPGroup ⟨p, hp⟩
    refine ⟨e, ?_⟩
    have : p ^ 2 ^ e = 1 := congrArg Subtype.val he
    rw [conj_pow, this]; group
  exact mem_of_isSylowTwoOf_of_le_normalizer (isSylowTwoOf_of_le_of_le hP (le_inf hP.le hPX)
    inf_le_left) hAX ⟨hxA, hxX⟩ h2

theorem sup_inf_le_normalizer_of_commuting {A B P₁ P₂ X : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hP₁ : IsSylowTwoOf P₁ A) (hP₂ : IsSylowTwoOf P₂ B)
    (hP₁X : P₁ ≤ X) (hP₂X : P₂ ≤ X) (hAX : A ⊓ X ≤ Subgroup.normalizer (P₁ : Set G))
    (hBX : B ⊓ X ≤ Subgroup.normalizer (P₂ : Set G)) :
    (A ⊔ B) ⊓ X ≤ Subgroup.normalizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) := by
  have hPP : P₂ ≤ Subgroup.normalizer (P₁ : Set G) :=
    le_normalizer_of_commute fun a ha b hb => hAB a (hP₁.le ha) b (hP₂.le hb)
  have hBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hAB a ha b hb).symm
  refine le_normalizer_of_conj_mem fun k hk y hy => ?_
  obtain ⟨p₁, hp₁, p₂, hp₂, rfl⟩ := (mem_sup_iff_of_le_normalizer hPP).mp hy
  have e : k * (p₁ * p₂) * k⁻¹ = (k * p₁ * k⁻¹) * (k * p₂ * k⁻¹) := by group
  rw [e]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · exact conj_mem_of_commuting hAB hP₁ hP₁X hAX hk.1 hk.2 hp₁
  · exact conj_mem_of_commuting hBA hP₂ hP₂X hBX (by rw [sup_comm]; exact hk.1) hk.2 hp₂

end Commuting

section Center

variable {G : Type*} [Group G]

theorem mem_of_forall_commute_of_isLin2Type {A P : Subgroup G} {n : ℕ} (hn : 0 < n)
    (hlin : IsLin2Type A n) (hP : IsSylowTwoOf P A) {z : G} (hzA : z ∈ A)
    (hz : ∀ a ∈ A, z * a = a * z) : z ∈ P := by
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαker, -⟩ := hlin
  have hcentral : α ⟨z, hzA⟩ ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := hαs g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hz a a.2).symm
  obtain ⟨r, hr2, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcentral
  have hr2' : r ^ 2 = 1 := by simpa using hr2
  have hr0 : r ≠ 0 := fun h => by simp [h] at hr2'
  have hferm := FiniteField.pow_card_sub_one_eq_one r hr0
  rw [hcard] at hferm
  obtain ⟨j, hj⟩ : ∃ j, 2 ^ n - 1 = 2 * j + 1 := by
    obtain ⟨c, hc⟩ : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 0 < 2 ^ n := by positivity
    exact ⟨c - 1, by omega⟩
  rw [hj, pow_succ, pow_mul, hr2', one_pow, one_mul] at hferm
  subst hferm
  have h1 : α ⟨z, hzA⟩ = 1 := by
    apply Subtype.ext
    rw [← hrA]
    simp
  have hmem : (⟨z, hzA⟩ : A) ∈ α.ker := h1
  rw [hαker] at hmem
  have hz' : z ∈ pCoreOf 2 A := ⟨⟨z, hzA⟩, by assumption, rfl⟩
  exact hP.pCoreOf_le hz'

end Center

section Hall

variable {G : Type*} [Group G] [Finite G]

theorem exists_hall_of_normal_sylow {K P : Subgroup G} (hP : IsSylowTwoOf P K)
    (hN : K ≤ Subgroup.normalizer (P : Set G)) : ∃ D : Subgroup G, IsHallTwoPrimeOf D K := by
  have : (P.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hP.le).mpr hN
  have hcardP : Nat.card (P.subgroupOf K) = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.le).toEquiv
  obtain ⟨e, he⟩ := hP.isPGroup.exists_card_eq
  have hidx : ¬ 2 ∣ (P.subgroupOf K).index := hP.2.2
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf K)) (P.subgroupOf K).index := by
    rw [hcardP, he]
    exact Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hidx)
  obtain ⟨D', hD'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hmul : Nat.card (P.subgroupOf K) * Nat.card D' = Nat.card K := hD'.card_mul_card
  have hmul' : (P.subgroupOf K).index * Nat.card (P.subgroupOf K) = Nat.card K :=
    Subgroup.index_mul_card _
  have hDcard : Nat.card D' = (P.subgroupOf K).index := by
    have hpos : 0 < Nat.card (P.subgroupOf K) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hmul, ← hmul', mul_comm]
  have hDindex : D'.index = 2 ^ e := by
    have h1 : D'.index * Nat.card D' = Nat.card K := Subgroup.index_mul_card _
    have hpos : 0 < Nat.card D' := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← hmul, hcardP, he]
  refine ⟨D'.map K.subtype, Subgroup.map_subtype_le D', ?_, ⟨e, ?_⟩⟩
  · rw [Subgroup.card_map_of_injective K.subtype_injective, hDcard]
    exact Nat.odd_iff.mpr (by omega)
  · change ((D'.map K.subtype).comap K.subtype).index = 2 ^ e
    rw [Subgroup.comap_map_eq_self_of_injective K.subtype_injective, hDindex]

end Hall

section Setting

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem S_le_M (hcs : ConstrainedSetting G T M H S L) : S ≤ M := fun _ hx => (hcs.sylow_inf.le hx).2

theorem isSylowTwoOf_S_inf_L (hcs : ConstrainedSetting G T M H S L) : IsSylowTwoOf (S ⊓ L) L :=
  RankOneRecog.isSylowTwoOf_inf_of_subnormal hcs.sylow hcs.block.1.2.1 hcs.block.1.2.2

theorem L_inf_M_le_normalizer (hcs : ConstrainedSetting G T M H S L) {n : ℕ} (hn : 0 < n)
    (hlin : IsLin2Type L n) : L ⊓ M ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
  inf_le_normalizer_of_isLin2Type hn hlin (isSylowTwoOf_S_inf_L hcs)
    (inf_le_left.trans (S_le_M hcs)) hcs.not_le

theorem sylow_and_normalizer_double (hcs : ConstrainedSetting G T M H S L) {n : ℕ} (hn : 0 < n)
    (hlin : IsLin2Type L n) {t : G} (ht : t ∈ S)
    (hK : conjJoin S L = L ⊔ L.map (MulAut.conj t).toMonoidHom)
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥) :
    IsSylowTwoOf (conjJoin S L ⊓ S) (conjJoin S L) ∧
      conjJoin S L ⊓ M ≤ Subgroup.normalizer ((conjJoin S L ⊓ S : Subgroup G) : Set G) := by
  set c : G ≃* G := MulAut.conj t with hc
  set L₂ : Subgroup G := L.map c.toMonoidHom with hL₂
  set P₁ : Subgroup G := S ⊓ L with hP₁def
  set P₂ : Subgroup G := P₁.map c.toMonoidHom with hP₂def
  have hcx : ∀ x : G, c.toMonoidHom x = t * x * t⁻¹ := fun x => by simp [hc, MulAut.conj_apply]
  have htM : t ∈ M := S_le_M hcs ht
  have hLc : L ≤ Subgroup.centralizer (L₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hAB : ∀ a ∈ L, ∀ b ∈ L₂, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hLc ha) b hb).symm
  have hP₁ : IsSylowTwoOf P₁ L := isSylowTwoOf_S_inf_L hcs
  have hP₂ : IsSylowTwoOf P₂ L₂ := hP₁.map_equiv c
  have hP₁M : P₁ ≤ M := inf_le_left.trans (S_le_M hcs)
  have hP₂S : P₂ ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hcx]
    exact S.mul_mem (S.mul_mem ht hx.1) (S.inv_mem ht)
  have hP₂M : P₂ ≤ M := hP₂S.trans (S_le_M hcs)
  have hF1 : L ⊓ M ≤ Subgroup.normalizer (P₁ : Set G) := L_inf_M_le_normalizer hcs hn hlin
  have hF2 : L₂ ⊓ M ≤ Subgroup.normalizer (P₂ : Set G) := by
    rintro _ ⟨⟨x₀, hx₀, rfl⟩, hxM⟩
    have hx₀M : x₀ ∈ M := by
      have h1 : t⁻¹ * (t * x₀ * t⁻¹) * t ∈ M := by
        rw [hcx] at hxM
        exact M.mul_mem (M.mul_mem (M.inv_mem htM) hxM) htM
      simpa [mul_assoc] using h1
    have h2 : x₀ ∈ Subgroup.normalizer (P₁ : Set G) := hF1 ⟨hx₀, hx₀M⟩
    rw [hP₂def, normalizer_map_equiv]
    exact ⟨x₀, h2, rfl⟩
  have hinf : L ⊓ L₂ ≤ P₁ ⊓ P₂ := by
    rintro x ⟨hxL, hxL₂⟩
    refine ⟨mem_of_forall_commute_of_isLin2Type hn hlin hP₁ hxL fun a ha =>
      (hAB a ha x hxL₂).symm, ?_⟩
    obtain ⟨x₀, hx₀, rfl⟩ := hxL₂
    have hx₀P : x₀ ∈ P₁ := by
      refine mem_of_forall_commute_of_isLin2Type hn hlin hP₁ hx₀ fun a ha => ?_
      have h1 := hAB (c.toMonoidHom x₀) hxL (c.toMonoidHom a) ⟨a, ha, rfl⟩
      rw [hcx, hcx] at h1
      have h2 : t * (x₀ * a) * t⁻¹ = t * (a * x₀) * t⁻¹ := by
        calc t * (x₀ * a) * t⁻¹ = t * x₀ * t⁻¹ * (t * a * t⁻¹) := by group
          _ = t * a * t⁻¹ * (t * x₀ * t⁻¹) := h1
          _ = t * (a * x₀) * t⁻¹ := by group
      simpa using h2
    exact ⟨x₀, hx₀P, rfl⟩
  have hsup : IsSylowTwoOf (P₁ ⊔ P₂) (L ⊔ L₂) := isSylowTwoOf_sup_of_commuting hAB hP₁ hP₂ hinf
  have hN : (L ⊔ L₂) ⊓ M ≤ Subgroup.normalizer ((P₁ ⊔ P₂ : Subgroup G) : Set G) :=
    sup_inf_le_normalizer_of_commuting hAB hP₁ hP₂ hP₁M hP₂M hF1 hF2
  have hQS : P₁ ⊔ P₂ ≤ S := sup_le inf_le_left hP₂S
  have hP₀ : (L ⊔ L₂) ⊓ S = P₁ ⊔ P₂ :=
    hsup.eq_of_le (le_inf hsup.le hQS) inf_le_left (hcs.sylow.isPGroup.to_le inf_le_right)
  rw [hK, hP₀]
  exact ⟨hsup, hN⟩

theorem lin2_sylow_and_normalizer (hcs : ConstrainedSetting G T M H S L) {n : ℕ} (hn : 1 < n)
    (hlin : IsLin2Type L n) :
    IsSylowTwoOf (conjJoin S L ⊓ S) (conjJoin S L) ∧
      conjJoin S L ⊓ M ≤ Subgroup.normalizer ((conjJoin S L ⊓ S : Subgroup G) : Set G) := by
  rcases hcs.blocks with hj | ⟨t, ht, -, hK, hcomm⟩
  · rw [hj, inf_comm L S]
    exact ⟨isSylowTwoOf_S_inf_L hcs, L_inf_M_le_normalizer hcs (by omega) hlin⟩
  · exact sylow_and_normalizer_double hcs (by omega) hlin ht hK hcomm

end Setting

theorem lin2HallExists : Lin2HallExists := by
  intro G _ _ T M H S L hcs n hn hlin
  obtain ⟨hsyl, hN⟩ := lin2_sylow_and_normalizer hcs hn hlin
  have hPK : conjJoin S L ⊓ S ≤ conjJoin S L ⊓ M := inf_le_inf_left _ (S_le_M hcs)
  have hsylK : IsSylowTwoOf (conjJoin S L ⊓ S) (conjJoin S L ⊓ M) :=
    isSylowTwoOf_of_le_of_le hsyl hPK inf_le_left
  obtain ⟨D, hD⟩ := exists_hall_of_normal_sylow hsylK hN
  exact ⟨D, hD, fun d hd => hN (hD.1 hd)⟩

end CFSG.QuasithinUnique.Lin2
