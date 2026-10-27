module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIaThreeDiag
public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

section Diag

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {u : Y}

omit [Finite Y] in
theorem L34MSide.mem_center_of_conjDiag_eq_one
    {h01 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj u).toMonoidHom, a * b = b * a}
    {h02 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a}
    {h12 : ∀ a ∈ L.map (MulAut.conj u).toMonoidHom,
      ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a}
    {l : L} (hl : conjDiag L u h01 h02 h12 l = 1) : l ∈ Subgroup.center L := by
  rw [conjDiag_apply] at hl
  have hlinv : (l : Y) = ((u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹))⁻¹ := by
    have : (l : Y) * ((u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹)) = 1 := by
      rw [← mul_assoc]; exact hl
    exact eq_inv_of_mul_eq_one_left this
  refine Subgroup.mem_center_iff.mpr fun a => Subtype.ext ?_
  simp only [Subgroup.coe_mul]
  have c1 := h01 a a.2 _ (conj_mem_map_conj u l.2)
  have c2 := h02 a a.2 _ (conj_mem_map_conj (u ^ 2) l.2)
  have hc : Commute (a : Y) ((u * l * u⁻¹) * (u ^ 2 * l * (u ^ 2)⁻¹)) :=
    (Commute.mul_right c1 c2)
  rw [hlinv]
  exact (hc.inv_right).eq

theorem L34MSide.dvd_card_range_conjDiag
    (h01 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj u).toMonoidHom, a * b = b * a)
    (h02 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a)
    (h12 : ∀ a ∈ L.map (MulAut.conj u).toMonoidHom,
      ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a) :
    Nat.card (L ⧸ Subgroup.center L) ∣ Nat.card (conjDiag L u h01 h02 h12).range := by
  set f := conjDiag L u h01 h02 h12 with hf
  have hker : f.ker ≤ Subgroup.center L := fun l hl =>
    L34MSide.mem_center_of_conjDiag_eq_one (MonoidHom.mem_ker.mp hl)
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hker
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hq : Nat.card (L ⧸ f.ker) = Nat.card (L ⧸ Subgroup.center L) * k := by
    rw [hk] at e1
    have : Nat.card (L ⧸ f.ker) * Nat.card f.ker =
        (Nat.card (L ⧸ Subgroup.center L) * k) * Nat.card f.ker := by
      rw [← e2, e1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hr : Nat.card f.range = Nat.card (L ⧸ f.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
  rw [hr, hq]
  exact Dvd.intro k rfl

theorem L34MSide.mem_normalizer_of_perfect_centralizer_not_dvd (n : ℕ)
    (hL : IsComponentOf L ⊤) (hu : u ^ 3 = 1) (hn : n ∣ Nat.card (L ⧸ Subgroup.center L))
    (hZ : ∀ D : Subgroup Y, ⁅D, D⁆ = D → D ≤ Subgroup.centralizer ({u} : Set Y) →
      ¬ n ∣ Nat.card D) :
    u ∈ Subgroup.normalizer (L : Set Y) := by
  by_contra hnot
  obtain ⟨h01', h02', h12'⟩ := map_conj_ne_of_not_mem_normalizer hu hnot
  have hc₁ := isComponentOf_map_conj hL u
  have hc₂ := isComponentOf_map_conj hL (u ^ 2)
  have c01 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj u).toMonoidHom, a * b = b * a :=
    fun a ha b hb => commute_of_mem_ne hL hc₁ h01' ha hb
  have c02 : ∀ a ∈ L, ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a :=
    fun a ha b hb => commute_of_mem_ne hL hc₂ h02' ha hb
  have c12 : ∀ a ∈ L.map (MulAut.conj u).toMonoidHom,
      ∀ b ∈ L.map (MulAut.conj (u ^ 2)).toMonoidHom, a * b = b * a :=
    fun a ha b hb => commute_of_mem_ne hc₁ hc₂ h12' ha hb
  set f := conjDiag L u c01 c02 c12 with hf
  have hLperf : ⁅(⊤ : Subgroup L), ⊤⁆ = ⊤ := hL.2.2.1
  have hDperf : ⁅f.range, f.range⁆ = f.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, hLperf]
  exact hZ f.range hDperf (range_conjDiag_le_centralizer (h01 := c01) (h02 := c02)
    (h12 := c12) hu) (hn.trans (L34MSide.dvd_card_range_conjDiag c01 c02 c12))

omit [Finite Y] in
theorem L34MSide.not_mem_centralizer_of_perfect_centralizer_not_dvd (n : ℕ)
    (hL : IsComponentOf L ⊤) (hn : n ∣ Nat.card (L ⧸ Subgroup.center L))
    (hZ : ∀ D : Subgroup Y, ⁅D, D⁆ = D → D ≤ Subgroup.centralizer ({u} : Set Y) →
      ¬ n ∣ Nat.card D) :
    u ∉ Subgroup.centralizer (L : Set Y) := by
  intro hu
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp (⟨hL.2.2.1⟩ : Group.IsPerfect ↥L)
  have hle : L ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hu l hl
  apply hZ L hLperf hle
  have e := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center L)
  rw [e]
  exact Dvd.dvd.mul_right hn _

end Diag

section Lift

variable {X : Type} [Group X] [Finite X]

theorem L34MSide.centralizer_mk_eq {x : X} (hx : IsPGroup 3 (Subgroup.zpowers x)) :
    Subgroup.centralizer ({QuotientGroup.mk' (primeComplementCore (G := X) 3) x} : Set _) =
      (Subgroup.centralizer ({x} : Set X)).map
        (QuotientGroup.mk' (primeComplementCore (G := X) 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (primeComplementCore_coprime (G := X) 3) h
  have h := CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 3)
    (N := primeComplementCore (G := X) 3) hN hx
  rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
  exact h

theorem L34MSide.not_dvd_card_of_perfect_le_centralizer_mk (n : ℕ) {x : X}
    (hx : IsPGroup 3 (Subgroup.zpowers x))
    (hperf : ∀ D : Subgroup X, D ≤ Subgroup.centralizer ({x} : Set X) → ⁅D, D⁆ = D →
      ¬ n ∣ Nat.card D)
    (D : Subgroup (X ⧸ primeComplementCore (G := X) 3)) (hDp : ⁅D, D⁆ = D)
    (hDC : D ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (primeComplementCore (G := X) 3) x} : Set _)) :
    ¬ n ∣ Nat.card D := by
  set π := QuotientGroup.mk' (primeComplementCore (G := X) 3) with hπ
  set C := Subgroup.centralizer ({x} : Set X) with hCdef
  rw [L34MSide.centralizer_mk_eq hx] at hDC
  set A := D.comap π ⊓ C with hA
  let f : A →* D := (π.comp A.subtype).codRestrict D (fun a => a.2.1)
  have hsurj : Function.Surjective f := by
    intro d
    obtain ⟨c, hcC, hcd⟩ := hDC d.2
    refine ⟨⟨c, ?_, hcC⟩, Subtype.ext hcd⟩
    show π c ∈ D
    rw [hcd]; exact d.2
  have : Group.IsPerfect ↥D := Subgroup.isPerfect_iff.mpr hDp
  have hmap := finite_perfectResidual_surjects_to_perfect_image f hsurj
  set W := (RankThreeCoreUniqueness.Helpers.perfectResidual A).map A.subtype with hW
  have hWC : W ≤ C := fun w hw => by
    obtain ⟨a, -, rfl⟩ := hw
    exact a.2.2
  have hPR : ⁅RankThreeCoreUniqueness.Helpers.perfectResidual A,
      RankThreeCoreUniqueness.Helpers.perfectResidual A⁆ =
        RankThreeCoreUniqueness.Helpers.perfectResidual A :=
    Subgroup.isPerfect_iff.mp finite_perfectResidual_isPerfect
  have hWp : ⁅W, W⁆ = W := by rw [hW, ← Subgroup.map_commutator, hPR]
  have hcop := hperf W hWC hWp
  have hdvd : Nat.card D ∣ Nat.card W := by
    have h1 : Nat.card D =
        Nat.card ((RankThreeCoreUniqueness.Helpers.perfectResidual A).map f) := by
      rw [hmap, Subgroup.card_top]
    have h2 : Nat.card W = Nat.card (RankThreeCoreUniqueness.Helpers.perfectResidual A) :=
      Subgroup.card_map_of_injective A.subtype_injective
    rw [h1, h2]
    exact Subgroup.card_map_dvd _ _
  exact fun h => hcop (h.trans hdvd)

theorem L34MSide.not_three_dvd_core : ¬ 3 ∣ Nat.card (primeComplementCore (G := X) 3) :=
  fun h => (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (primeComplementCore_coprime (G := X) 3) h

theorem L34MSide.mk_eq_of_pGroup {Q : Subgroup X} (hQ : IsPGroup 3 Q) {a b : X} (ha : a ∈ Q)
    (hb : b ∈ Q)
    (h : QuotientGroup.mk' (primeComplementCore (G := X) 3) a =
      QuotientGroup.mk' (primeComplementCore (G := X) 3) b) : a = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
    (L34MSide.not_three_dvd_core (X := X)) hQ
  have := hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) h
  exact congrArg Subtype.val this

theorem L34MSide.card_map_mk_of_pGroup {Q : Subgroup X} (hQ : IsPGroup 3 Q) :
    Nat.card (Q.map (QuotientGroup.mk' (primeComplementCore (G := X) 3))) = Nat.card Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := CFSG.GroupTheory.SteinbergBS.injective_mk'_comp_subtype
    (L34MSide.not_three_dvd_core (X := X)) hQ
  have e : Q.map (QuotientGroup.mk' (primeComplementCore (G := X) 3)) =
      ((QuotientGroup.mk' (primeComplementCore (G := X) 3)).comp Q.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [e]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem L34MSide.card_le_of_pGroup_le_centralizer_mk {x : X}
    (hx : IsPGroup 3 (Subgroup.zpowers x))
    {m : ℕ} (hm : ∀ Q : Subgroup X, Q ≤ Subgroup.centralizer ({x} : Set X) → IsPGroup 3 Q →
      Nat.card Q ≤ m)
    {Qt : Subgroup (X ⧸ primeComplementCore (G := X) 3)}
    (hQC : Qt ≤ Subgroup.centralizer
      ({QuotientGroup.mk' (primeComplementCore (G := X) 3) x} : Set _))
    (hQp : IsPGroup 3 Qt) : Nat.card Qt ≤ m := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := X) 3) with hπ
  rw [L34MSide.centralizer_mk_eq hx] at hQC
  set C := Subgroup.centralizer ({x} : Set X) with hCdef
  set A := Qt.comap π ⊓ C with hA
  have hAQ : A.map π = Qt := by
    refine le_antisymm (fun q hq => ?_) (fun q hq => ?_)
    · obtain ⟨a, ha, rfl⟩ := hq
      exact ha.1
    · obtain ⟨c, hcC, hcq⟩ := hQC hq
      have hcQ : c ∈ Qt.comap π := by
        show π c ∈ Qt
        rw [hπ, hcq]; exact hq
      exact ⟨c, ⟨hcQ, hcC⟩, hcq⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hdvd : Nat.card Qt ∣ Nat.card A := by rw [← hAQ]; exact Subgroup.card_map_dvd _ _
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 3 A))
  have hS := Sylow.pow_dvd_card_of_pow_dvd_card S (n := k) (by rw [← hk]; exact hdvd)
  set SX := (S : Subgroup A).map A.subtype with hSX
  have hSXp : IsPGroup 3 SX := S.isPGroup'.map _
  have hSXC : SX ≤ C := fun s hs => by
    obtain ⟨a, -, rfl⟩ := hs
    exact a.2.2
  have hcardS : Nat.card SX = Nat.card (S : Subgroup A) :=
    Subgroup.card_map_of_injective A.subtype_injective
  have h1 := hm SX hSXC hSXp
  rw [hk]
  rw [hcardS] at h1
  exact (Nat.le_of_dvd (Nat.card_pos) hS).trans h1

end Lift

theorem L34MSide.isPGroup_zpowers_of_orderOf {G : Type} [Group G] {M : Subgroup G} {z : G}
    (hzM : z ∈ M) (hz3 : orderOf z = 3) :
    IsPGroup 3 (Subgroup.zpowers (⟨z, hzM⟩ : M)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, pow_one]
  rw [← hz3]
  exact (orderOf_injective M.subtype M.subtype_injective ⟨z, hzM⟩).symm

end CFSG.AGLEmbedding
