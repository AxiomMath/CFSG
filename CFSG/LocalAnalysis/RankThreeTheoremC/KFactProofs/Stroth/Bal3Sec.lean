module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

@[expose] def NoSimpleSec (p : ℕ) (X : Type*) [Group X] : Prop :=
  ∀ (U : Subgroup X) (V : Subgroup U) [V.Normal], IsSimpleGroup (U ⧸ V) →
    (∃ a b : U ⧸ V, a * b ≠ b * a) → ¬ p ∣ Nat.card (U ⧸ V)

namespace NoSimpleSec

theorem not_dvd_of_surjective {X : Type*} [Group X] {p : ℕ} (h : NoSimpleSec p X)
    (G : Subgroup X) {S : Type*} [Group S] [IsSimpleGroup S] (φ : G →* S)
    (hφ : Function.Surjective φ) (hnonab : ∃ a b : S, a * b ≠ b * a) : ¬ p ∣ Nat.card S := by
  let e : G ⧸ φ.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  have hs : IsSimpleGroup (G ⧸ φ.ker) := e.isSimpleGroup
  have hnab : ∃ a b : G ⧸ φ.ker, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e.symm a, e.symm b, fun hc => hab ?_⟩
    simpa using congrArg e hc
  rw [← Nat.card_congr e.toEquiv]
  exact h G φ.ker hs hnab

theorem not_dvd_of_surjective_of_ker_le {X K S : Type*} [Group X] [Group K] [Group S]
    [IsSimpleGroup S] {p : ℕ} (h : NoSimpleSec p X) (ρ : K →* X) (φ : K →* S)
    (hφ : Function.Surjective φ) (hker : ρ.ker ≤ φ.ker)
    (hnonab : ∃ a b : S, a * b ≠ b * a) : ¬ p ∣ Nat.card S := by
  have hker' : ρ.rangeRestrict.ker ≤ φ.ker := by rwa [MonoidHom.ker_rangeRestrict]
  refine h.not_dvd_of_surjective ρ.range
    (ρ.rangeRestrict.liftOfSurjective ρ.rangeRestrict_surjective ⟨φ, hker'⟩) ?_ hnonab
  intro s
  obtain ⟨k, rfl⟩ := hφ s
  exact ⟨ρ.rangeRestrict k, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩

theorem of_injective {X Y : Type*} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    (hf : Function.Injective f) (hY : NoSimpleSec p Y) : NoSimpleSec p X := by
  intro U V _ hs hnab hp
  have hinj : Function.Injective (f.comp U.subtype) := hf.comp U.subtype_injective
  refine hY.not_dvd_of_surjective_of_ker_le (f.comp U.subtype) (QuotientGroup.mk' V)
    (QuotientGroup.mk'_surjective V) ?_ hnab hp
  rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
  exact bot_le

theorem of_mulEquiv {X Y : Type*} [Group X] [Group Y] {p : ℕ} (e : X ≃* Y)
    (hY : NoSimpleSec p Y) : NoSimpleSec p X :=
  of_injective e.toMonoidHom e.injective hY

theorem of_surjective {X Y : Type*} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hX : NoSimpleSec p X) : NoSimpleSec p Y := by
  intro U V _ hs hnab hp
  refine hX.not_dvd_of_surjective (U.comap f) ((QuotientGroup.mk' V).comp (f.subgroupComap U))
    ?_ hnab hp
  intro s
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective V s
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨⟨x, hy⟩, rfl⟩

theorem of_isSolvable {X : Type*} [Group X] [Group.IsSolvable X] (p : ℕ) : NoSimpleSec p X := by
  intro U V _ hs hnab _
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := U ⧸ V)).2 inferInstance a b)

theorem of_subsingleton {X : Type*} [Group X] [Subsingleton X] (p : ℕ) : NoSimpleSec p X :=
  of_isSolvable p

theorem of_not_dvd {X : Type*} [Group X] [Finite X] {p : ℕ} (h : ¬ p ∣ Nat.card X) :
    NoSimpleSec p X := by
  intro U V _ _ _ hp
  exact h (hp.trans ((Subgroup.card_quotient_dvd_card V).trans (Subgroup.card_subgroup_dvd_card U)))

theorem of_extension {X : Type*} [Group X] {p : ℕ} (N : Subgroup X) [N.Normal]
    (hN : NoSimpleSec p N) (hQ : NoSimpleSec p (X ⧸ N)) : NoSimpleSec p X := by
  intro U V _ hs hnab hp
  let π : U →* U ⧸ V := QuotientGroup.mk' V
  let W : Subgroup U := N.subgroupOf U
  haveI : (W.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective V)
  rcases hs.eq_bot_or_eq_top_of_normal (W.map π) with h | h
  ·
    have hWV : W ≤ V := by
      have := (Subgroup.map_eq_bot_iff W).1 h
      rwa [QuotientGroup.ker_mk'] at this
    refine hQ.not_dvd_of_surjective_of_ker_le ((QuotientGroup.mk' N).comp U.subtype) π
      (QuotientGroup.mk'_surjective V) ?_ hnab hp
    intro u hu
    have huN : (u : X) ∈ N := by
      simpa [MonoidHom.mem_ker, QuotientGroup.eq_one_iff] using hu
    have huV : u ∈ V := hWV huN
    simpa [π] using huV
  ·
    have hsurj : Function.Surjective (π.comp W.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
      exact h
    let ρ : W →* N := (U.subtype.comp W.subtype).codRestrict N (fun w => w.2)
    have hρ : Function.Injective ρ := by
      intro a b hab
      have h' := congrArg (fun n : N => (n : X)) hab
      exact Subtype.ext (Subtype.ext h')
    refine hN.not_dvd_of_surjective_of_ker_le ρ (π.comp W.subtype) hsurj ?_ hnab hp
    rw [(MonoidHom.ker_eq_bot_iff ρ).2 hρ]
    exact bot_le

theorem of_surjective_ker {X Y : Type*} [Group X] [Group Y] {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hK : NoSimpleSec p f.ker) (hY : NoSimpleSec p Y) :
    NoSimpleSec p X :=
  of_extension f.ker hK (of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective f hf) hY)

theorem of_surjective_coprime_ker {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    (f : X →* Y) (hf : Function.Surjective f) (hker : ¬ p ∣ Nat.card f.ker)
    (hY : NoSimpleSec p Y) : NoSimpleSec p X :=
  of_surjective_ker f hf (of_not_dvd hker) hY

theorem of_hasNormalPComplement {X : Type*} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : CFSG.HasNormalPComplement p X) : NoSimpleSec p X := by
  obtain ⟨N, hN, hcop, hpg⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent (X ⧸ N) := hpg.isNilpotent
  exact of_extension N (of_not_dvd (hp.coprime_iff_not_dvd.1 hcop)) (of_isSolvable p)

theorem prod {X Y : Type*} [Group X] [Group Y] {p : ℕ} (hX : NoSimpleSec p X)
    (hY : NoSimpleSec p Y) : NoSimpleSec p (X × Y) := by
  refine of_surjective_ker (MonoidHom.fst X Y) (fun x => ⟨(x, 1), rfl⟩) ?_ hX
  refine of_injective ((MonoidHom.snd X Y).comp (MonoidHom.fst X Y).ker.subtype) ?_ hY
  rintro ⟨⟨a₁, a₂⟩, ha⟩ ⟨⟨b₁, b₂⟩, hb⟩ hab
  have ha₁ : a₁ = 1 := ha
  have hb₁ : b₁ = 1 := hb
  have h₂ : a₂ = b₂ := hab
  subst ha₁ hb₁ h₂
  rfl

end NoSimpleSec

theorem not_noSimpleSec_of_surjective {X : Type*} [Group X] {p : ℕ} (G : Subgroup X)
    {S : Type*} [Group S] [IsSimpleGroup S] (φ : G →* S) (hφ : Function.Surjective φ)
    (hnonab : ∃ a b : S, a * b ≠ b * a) [Finite S] (hp : p ∣ Nat.card S) :
    ¬ NoSimpleSec p X :=
  fun h => h.not_dvd_of_surjective G φ hφ hnonab hp

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
