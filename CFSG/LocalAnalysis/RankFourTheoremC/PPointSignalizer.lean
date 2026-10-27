module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding Subgroup

theorem card_le_of_isCyclic_of_pow_eq_one {H : Type*} [Group H] [Finite H] [IsCyclic H] {p : ℕ}
    (hp : 0 < p) (h : ∀ x : H, x ^ p = 1) : Nat.card H ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
  exact Nat.le_of_dvd hp (orderOf_dvd_of_pow_eq_one (h g))

theorem isElemAbelian_of_le {G : Type*} [Group G] {p : ℕ} {A B : Subgroup G}
    (hA : IsElemAbelian p A) (h : B ≤ A) : IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hA h

theorem exists_plane_of_mem {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B : Subgroup G} (hB : IsElemAbelian p B) (hcard : p ^ 2 ≤ Nat.card B) {b : G} (hb : b ∈ B) :
    ∃ B₀ : Subgroup G, B₀ ≤ B ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧ b ∈ B₀ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hex : ∃ b₁ ∈ B, b₁ ≠ 1 ∧ b ∈ zpowers b₁ := by
    by_cases hb1 : b = 1
    · have : B ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard
        have := hp.one_lt
        have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) this
        omega
      obtain ⟨⟨b₁, hb₁⟩, h1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp this
      exact ⟨b₁, hb₁, fun h => h1 (Subtype.ext h), hb1 ▸ one_mem _⟩
    · exact ⟨b, hb, hb1, mem_zpowers b⟩
  obtain ⟨b₁, hb₁, hb₁1, hbb₁⟩ := hex
  have hb₁p : b₁ ^ p = 1 := hB.2 b₁ hb₁
  have hzcard : Nat.card (zpowers b₁) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hb₁p hb₁1]
  have hex2 : ∃ b₂ ∈ B, b₂ ∉ zpowers b₁ := by
    by_contra hall
    push Not at hall
    have : B ≤ zpowers b₁ := hall
    have := Subgroup.card_le_of_le this
    rw [hzcard] at this
    have hp1 := hp.one_lt
    have : p < p ^ 2 := by nlinarith
    omega
  obtain ⟨b₂, hb₂, hb₂z⟩ := hex2
  have hb₂p : b₂ ^ p = 1 := hB.2 b₂ hb₂
  have hcomm : ∀ e ∈ zpowers b₁, e * b₂ = b₂ * e := fun e he => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp he
    exact (Commute.zpow_left (show Commute b₁ b₂ from
      congrArg Subtype.val (hB.1.is_comm.comm ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩)) k).eq
  have hle : zpowers b₁ ⊔ zpowers b₂ ≤ B := sup_le (zpowers_le.mpr hb₁) (zpowers_le.mpr hb₂)
  refine ⟨zpowers b₁ ⊔ zpowers b₂, hle, isElemAbelian_of_le hB hle, ?_, ?_⟩
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (zpowers b₁) hb₂p hb₂z hcomm, hzcard]
    ring
  · exact (le_sup_left : zpowers b₁ ≤ zpowers b₁ ⊔ zpowers b₂) hbb₁

theorem mem_ker_conjNormal {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {g : X} :
    g ∈ (MulAut.conjNormal : X →* MulAut K).ker ↔ g ∈ centralizer (K : Set X) := by
  rw [MonoidHom.mem_ker, mem_centralizer_iff, MulEquiv.ext_iff]
  constructor
  · intro h k hk
    have := congrArg Subtype.val (h ⟨k, hk⟩)
    rw [MulAut.conjNormal_apply] at this
    simp only [MulAut.one_apply] at this
    calc k * g = (g * k * g⁻¹) * g := by rw [this]
      _ = g * k := by group
  · intro h k
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    simp only [MulAut.one_apply]
    calc g * (k : X) * g⁻¹ = ((k : X) * g) * g⁻¹ := by rw [← h k k.2]
      _ = k := by group

theorem commute_of_coprime_of_card {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hsig : GL83SignalizerAut) {K : Subgroup X} (hKn : K.Normal)
    {i : TauCeti.CFSGIndex} (hi : GL83Type24 p i) (e : Nonempty (K ≃* i.Group))
    (hDp : IsPGroup p (centralizer (K : Set X))) (hDc : IsCyclic (centralizer (K : Set X)))
    {E F : Subgroup X} (hE : IsElemAbelian p E) (hE3 : p ^ 3 ≤ Nat.card E)
    (hEin : GL83OuterType24 p i ∨ ∀ a ∈ E, a ∈ K ⊔ centralizer (K : Set X))
    (hF : p.Coprime (Nat.card F)) (hEF : E ≤ normalizer (F : Set X)) :
    ∀ a ∈ E, ∀ f ∈ F, a * f = f * a := by
  have hp : p.Prime := Fact.out
  have := hKn
  set D : Subgroup X := centralizer (K : Set X) with hD
  set φ : X →* MulAut K := MulAut.conjNormal with hφ
  have hker : ∀ g, g ∈ φ.ker ↔ g ∈ D := fun g => mem_ker_conjNormal
  set ψ : E →* MulAut K := φ.comp E.subtype with hψ
  have hBel : IsElemAbelian p ψ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      apply Subtype.ext
      change (a : MulAut K) * b = b * a
      rw [← ha', ← hb', ← map_mul, ← map_mul]
      congr 1
      exact hE.1.is_comm.comm a' b'
    · rintro _ ⟨a', rfl⟩
      rw [← map_pow]
      have : a' ^ p = 1 := Subtype.ext (hE.2 a' a'.2)
      rw [this, map_one]
  have hker_card : Nat.card ψ.ker ≤ p := by
    let κ : ψ.ker →* D :=
      ((E.subtype.comp ψ.ker.subtype).codRestrict D fun x => (hker _).mp x.2)
    have hκ : Function.Injective κ := by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (Subtype.val : D → X) hxy))
    have : IsCyclic ψ.ker := isCyclic_of_injective κ hκ
    exact card_le_of_isCyclic_of_pow_eq_one hp.pos fun x => Subtype.ext (Subtype.ext (hE.2 _ x.1.2))
  have hBcard : p ^ 2 ≤ Nat.card ψ.range := by
    have h := Subgroup.card_ker_mul_card_range ψ
    by_contra hlt
    push Not at hlt
    have hp1 := hp.one_lt
    have : Nat.card ψ.ker * Nat.card ψ.range < p ^ 3 := by
      calc Nat.card ψ.ker * Nat.card ψ.range ≤ p * Nat.card ψ.range :=
            Nat.mul_le_mul_right _ hker_card
        _ < p * p ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hp.pos
        _ = p ^ 3 := by ring
    omega
  intro a ha f hf
  have haB : φ a ∈ ψ.range := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨B₀, hB₀B, hB₀el, hB₀card, haB₀⟩ := exists_plane_of_mem hp hBel hBcard haB
  set Y : Subgroup (MulAut K) := F.map φ with hY
  have hYcop : p.Coprime (Nat.card Y) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd F φ) hF
  have hB₀N : B₀ ≤ normalizer (Y : Set (MulAut K)) := by
    intro b hb
    obtain ⟨⟨a', ha'⟩, rfl⟩ := hB₀B hb
    exact Subgroup.le_normalizer_map φ ⟨a', hEF ha', rfl⟩
  have hinner : B₀ ≤ (MulAut.conj : K →* MulAut K).range ∨ GL83OuterType24 p i := by
    rcases hEin with hout | hin
    · exact Or.inr hout
    · refine Or.inl fun b hb => ?_
      obtain ⟨⟨a', ha'⟩, rfl⟩ := hB₀B hb
      obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp (hin a' ha')
      refine ⟨⟨k, hk⟩, ?_⟩
      have hφc : φ c = 1 := MonoidHom.mem_ker.mp ((hker c).mpr hc)
      change MulAut.conj (⟨k, hk⟩ : K) = φ a'
      rw [← hkc, map_mul, hφc, mul_one, ← MulAut.conjNormal_val]
  have hcent : B₀ ≤ centralizer (Y : Set (MulAut K)) :=
    hsig K p i hp hp2 hi e B₀ Y hB₀el hB₀card hYcop hB₀N hinner
  have hcomm : φ a * φ f = φ f * φ a :=
    (mem_centralizer_iff.mp (hcent haB₀) (φ f) ⟨f, hf, rfl⟩).symm
  have hfa : a * f * a⁻¹ ∈ F := ((mem_normalizer_iff.mp (hEF ha)) f).mp hf
  have hcom : a * f * a⁻¹ * f⁻¹ ∈ F ⊓ D := by
    refine ⟨F.mul_mem hfa (F.inv_mem hf), (hker _).mp ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    calc φ a * φ f * (φ a)⁻¹ * (φ f)⁻¹ = φ f * φ a * (φ a)⁻¹ * (φ f)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  obtain ⟨n, hn⟩ := hDp.exists_card_eq
  have hbot : F ⊓ D = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (by
    rw [hn]; exact (Nat.Coprime.symm hF).pow_right n))
  rw [hbot, mem_bot] at hcom
  have := mul_inv_eq_one.mp hcom
  exact (mul_inv_eq_iff_eq_mul.mp this)

end CFSG.LocalAnalysis.RankFourTheoremC
